-- STATUS: main-path (the terminal planar rule: supports, fibre partners, local maps)
import TorusEven.D5.Schedule
import TorusEven.D3.RouteE

/-!
# The terminal plane (manuscript §8.3, Lemma `lem:d5-endpoint`)

Points of the plane are `(a, b) ∈ ZMod m × ZMod m`.  With `a_0 = (1,0)`, `a_1 = (0,1)`,
`a_2 = (0,0)` the local map of colour `i` is `j_i(q) = q - a_i + a_{ω(q)(i)}`, supported on
`B_i = {q : ω(q)(i) ≠ i}`.  The quotient functionals are `ℓ_0 = a`, `ℓ_1 = b`, `ℓ_2 = a + b`.
Each `ℓ_i`-fibre meets `B_i` in exactly two points, exchanged by the explicit involution
`partner_i`; the composite `partner_i ∘ j_i` is a single `2m`-cycle on `B_i`.
This file: definitions, the `ω` table on the point families, and colour `i = 0`.
-/

namespace TorusEven
namespace D5

variable {m : ℕ} [NeZero m]

abbrev Pt (m : ℕ) := ZMod m × ZMod m

def ptA : Pt m := (0, 2)
def ptB : Pt m := (0, 3)
def ptC : Pt m := (2, 1)
def ptX (t : ZMod m) : Pt m := (t, 2)
def ptY (t : ZMod m) : Pt m := (1, t)
def ptZ (t : ZMod m) : Pt m := (t, 3 - t)

def avec : Fin 3 → Pt m := ![(1, 0), (0, 1), (0, 0)]

/-- The local map `j_i`. -/
def jmap (i : Fin 3) (q : Pt m) : Pt m := q - avec i + avec (omega q i)

/-- The support `B_i`. -/
def inB (i : Fin 3) (q : Pt m) : Prop := omega q i ≠ i

theorem jmap_of_not_inB {i : Fin 3} {q : Pt m} (h : ¬ inB i q) : jmap i q = q := by
  unfold inB at h
  push_neg at h
  simp [jmap, h]

/-! ### Constants -/

theorem const_ne (h6 : 6 ≤ m) {a b : ℕ} (hab : a ≠ b) (ha : a < 6) (hb : b < 6) :
    ((a : ℕ) : ZMod m) ≠ ((b : ℕ) : ZMod m) := by
  intro h
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  exact hab h

/-! ### The `ω` table on the families (for `m ≥ 6`) -/
section omegaTable

variable (h6 : 6 ≤ m)
include h6

theorem c01 : (0 : ZMod m) ≠ 1 := by simpa using const_ne h6 (a := 0) (b := 1) (by decide) (by decide) (by decide)
theorem c02 : (0 : ZMod m) ≠ 2 := by simpa using const_ne h6 (a := 0) (b := 2) (by decide) (by decide) (by decide)
theorem c03 : (0 : ZMod m) ≠ 3 := by simpa using const_ne h6 (a := 0) (b := 3) (by decide) (by decide) (by decide)
theorem c12 : (1 : ZMod m) ≠ 2 := by simpa using const_ne h6 (a := 1) (b := 2) (by decide) (by decide) (by decide)
theorem c13 : (1 : ZMod m) ≠ 3 := by simpa using const_ne h6 (a := 1) (b := 3) (by decide) (by decide) (by decide)
theorem c23 : (2 : ZMod m) ≠ 3 := by simpa using const_ne h6 (a := 2) (b := 3) (by decide) (by decide) (by decide)
theorem c14 : (1 : ZMod m) ≠ 4 := by simpa using const_ne h6 (a := 1) (b := 4) (by decide) (by decide) (by decide)
theorem c24 : (2 : ZMod m) ≠ 4 := by simpa using const_ne h6 (a := 2) (b := 4) (by decide) (by decide) (by decide)
theorem c34 : (3 : ZMod m) ≠ 4 := by simpa using const_ne h6 (a := 3) (b := 4) (by decide) (by decide) (by decide)
theorem c04 : (0 : ZMod m) ≠ 4 := by simpa using const_ne h6 (a := 0) (b := 4) (by decide) (by decide) (by decide)
theorem c05 : (0 : ZMod m) ≠ 5 := by simpa using const_ne h6 (a := 0) (b := 5) (by decide) (by decide) (by decide)
theorem c15 : (1 : ZMod m) ≠ 5 := by simpa using const_ne h6 (a := 1) (b := 5) (by decide) (by decide) (by decide)
theorem c25 : (2 : ZMod m) ≠ 5 := by simpa using const_ne h6 (a := 2) (b := 5) (by decide) (by decide) (by decide)
theorem c35 : (3 : ZMod m) ≠ 5 := by simpa using const_ne h6 (a := 3) (b := 5) (by decide) (by decide) (by decide)

/-- All the inequalities among `0,…,5`, both orientations, for `simp`. -/
theorem consts :
    (0 : ZMod m) ≠ 1 ∧ (1 : ZMod m) ≠ 0 ∧ (0 : ZMod m) ≠ 2 ∧ (2 : ZMod m) ≠ 0 ∧
    (0 : ZMod m) ≠ 3 ∧ (3 : ZMod m) ≠ 0 ∧ (1 : ZMod m) ≠ 2 ∧ (2 : ZMod m) ≠ 1 ∧
    (1 : ZMod m) ≠ 3 ∧ (3 : ZMod m) ≠ 1 ∧ (2 : ZMod m) ≠ 3 ∧ (3 : ZMod m) ≠ 2 ∧
    (1 : ZMod m) ≠ 4 ∧ (4 : ZMod m) ≠ 1 ∧ (2 : ZMod m) ≠ 4 ∧ (4 : ZMod m) ≠ 2 ∧
    (3 : ZMod m) ≠ 4 ∧ (4 : ZMod m) ≠ 3 ∧ (0 : ZMod m) ≠ 4 ∧ (4 : ZMod m) ≠ 0 ∧
    (0 : ZMod m) ≠ 5 ∧ (5 : ZMod m) ≠ 0 ∧ (1 : ZMod m) ≠ 5 ∧ (5 : ZMod m) ≠ 1 ∧
    (2 : ZMod m) ≠ 5 ∧ (5 : ZMod m) ≠ 2 ∧ (3 : ZMod m) ≠ 5 ∧ (5 : ZMod m) ≠ 3 :=
  ⟨c01 h6, (c01 h6).symm, c02 h6, (c02 h6).symm, c03 h6, (c03 h6).symm, c12 h6, (c12 h6).symm,
   c13 h6, (c13 h6).symm, c23 h6, (c23 h6).symm, c14 h6, (c14 h6).symm, c24 h6, (c24 h6).symm,
   c34 h6, (c34 h6).symm, c04 h6, (c04 h6).symm, c05 h6, (c05 h6).symm, c15 h6, (c15 h6).symm,
   c25 h6, (c25 h6).symm, c35 h6, (c35 h6).symm⟩

theorem omega_A : omega (ptA : Pt m) = p201 := by
  have hc := consts h6
  simp [omega, ptA, hc]

theorem omega_B : omega (ptB : Pt m) = p120 := by
  have hc := consts h6
  simp [omega, ptB, hc]

theorem omega_C : omega (ptC : Pt m) = p201 := by
  have hc := consts h6
  simp [omega, ptC, hc]

theorem omega_Y1 : omega (ptY 1 : Pt m) = p120 := by
  have hc := consts h6
  simp [omega, ptY, hc]

theorem omega_Y3 : omega (ptY 3 : Pt m) = p201 := by
  have hc := consts h6
  simp [omega, ptY, hc]

theorem omega_Y0 : omega (ptY 0 : Pt m) = p021 := by
  have hc := consts h6
  simp [omega, ptY, hc]

theorem omega_X2 : omega (ptX 2 : Pt m) = p120 := by
  have hc := consts h6
  simp [omega, ptX, hc]

theorem omega_X (t : ZMod m) (h0 : t ≠ 0) (h1 : t ≠ 1) (h2 : t ≠ 2) :
    omega (ptX t) = p210 := by
  have hc := consts h6
  simp [omega, ptX, hc, h0, h1, h2]

theorem omega_Z (t : ZMod m) (h0 : t ≠ 0) (h1 : t ≠ 1) (h2 : t ≠ 2) :
    omega (ptZ t) = p102 := by
  have hc := consts h6
  by_cases h3 : t = 3
  · subst h3
    simp [omega, ptZ, hc]
  · have h4 : (3 : ZMod m) - t ≠ 0 := fun h => h3 (by linear_combination -h)
    have h5 : (3 : ZMod m) - t ≠ 1 := fun h => h2 (by linear_combination -h)
    have h6' : (3 : ZMod m) - t ≠ 2 := fun h => h1 (by linear_combination -h)
    have h7 : (3 : ZMod m) - t ≠ 3 := fun h => h0 (by linear_combination -h)
    simp [omega, ptZ, hc, h0, h1, h2, h3, h4, h5, h6', h7]

theorem omega_Y (t : ZMod m) (h0 : t ≠ 0) (h1 : t ≠ 1) (h2 : t ≠ 2) (h3 : t ≠ 3) :
    omega (ptY t) = p021 := by
  have hc := consts h6
  simp [omega, ptY, hc, h0, h1, h2, h3]

end omegaTable

/-! ### Casts of natural indices -/

theorem neg_cast_ne_cast {k c : ℕ} (h1 : 0 < k + c) (h2 : k + c < m) :
    -((k : ℕ) : ZMod m) ≠ ((c : ℕ) : ZMod m) := by
  intro h
  have h' : (((k + c : ℕ)) : ZMod m) = 0 := by
    rw [Nat.cast_add]
    linear_combination -h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact absurd (Nat.le_of_dvd h1 h') (by omega)

theorem cast_sub_self {k : ℕ} (hk : k ≤ m) : (((m - k : ℕ)) : ZMod m) = -((k : ℕ) : ZMod m) := by
  rw [Nat.cast_sub hk, ZMod.natCast_self, zero_sub]


/-! ### Reading the `ω` table -/

/-- Every point falls into exactly one branch of the `ω` table. -/
theorem omega_cases (q : Pt m) :
    (q.1 = 1 ∧ q.2 = 0 ∧ omega q = p021) ∨
    (q.1 = 3 ∧ q.2 = 0 ∧ omega q = p102) ∨
    (q.1 = 1 ∧ q.2 = 1 ∧ omega q = p120) ∨
    (q.1 = 2 ∧ q.2 = 1 ∧ omega q = p201) ∨
    (q.1 = 0 ∧ q.2 = 2 ∧ omega q = p201) ∨
    (q.1 = 2 ∧ q.2 = 2 ∧ omega q = p120) ∨
    (q.1 = 0 ∧ q.2 = 3 ∧ omega q = p120) ∨
    (q.1 = 1 ∧ q.2 = 3 ∧ omega q = p201) ∨
    (q.2 = 2 ∧ q.1 ≠ 0 ∧ q.1 ≠ 1 ∧ q.1 ≠ 2 ∧ omega q = p210) ∨
    (q.1 = 1 ∧ q.2 ≠ 0 ∧ q.2 ≠ 1 ∧ q.2 ≠ 2 ∧ q.2 ≠ 3 ∧ omega q = p021) ∨
    (q.1 + q.2 = 3 ∧ q.2 ≠ 0 ∧ q.2 ≠ 1 ∧ q.2 ≠ 2 ∧ q.2 ≠ 3 ∧ omega q = p102) ∨
    omega q = p012 := by
  set w := omega q with hw
  unfold omega at hw
  dsimp only at hw
  by_cases h1 : q.1 = 1 ∧ q.2 = 0
  · rw [if_pos h1] at hw
    exact Or.inl (⟨h1.1, h1.2, hw⟩)
  rw [if_neg h1] at hw
  by_cases h2 : q.1 = 3 ∧ q.2 = 0
  · rw [if_pos h2] at hw
    exact Or.inr (Or.inl (⟨h2.1, h2.2, hw⟩))
  rw [if_neg h2] at hw
  by_cases h3 : q.1 = 1 ∧ q.2 = 1
  · rw [if_pos h3] at hw
    exact Or.inr (Or.inr (Or.inl (⟨h3.1, h3.2, hw⟩)))
  rw [if_neg h3] at hw
  by_cases h4 : q.1 = 2 ∧ q.2 = 1
  · rw [if_pos h4] at hw
    exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h4.1, h4.2, hw⟩))))
  rw [if_neg h4] at hw
  by_cases h5 : q.1 = 0 ∧ q.2 = 2
  · rw [if_pos h5] at hw
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h5.1, h5.2, hw⟩)))))
  rw [if_neg h5] at hw
  by_cases h6 : q.1 = 2 ∧ q.2 = 2
  · rw [if_pos h6] at hw
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h6.1, h6.2, hw⟩))))))
  rw [if_neg h6] at hw
  by_cases h7 : q.1 = 0 ∧ q.2 = 3
  · rw [if_pos h7] at hw
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h7.1, h7.2, hw⟩)))))))
  rw [if_neg h7] at hw
  by_cases h8 : q.1 = 1 ∧ q.2 = 3
  · rw [if_pos h8] at hw
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h8.1, h8.2, hw⟩))))))))
  rw [if_neg h8] at hw
  by_cases h9 : q.2 = 2 ∧ q.1 ≠ 0 ∧ q.1 ≠ 1 ∧ q.1 ≠ 2
  · rw [if_pos h9] at hw
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h9.1, h9.2.1, h9.2.2.1, h9.2.2.2, hw⟩)))))))))
  rw [if_neg h9] at hw
  by_cases h10 : q.1 = 1 ∧ q.2 ≠ 0 ∧ q.2 ≠ 1 ∧ q.2 ≠ 2 ∧ q.2 ≠ 3
  · rw [if_pos h10] at hw
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h10.1, h10.2.1, h10.2.2.1, h10.2.2.2.1, h10.2.2.2.2, hw⟩))))))))))
  rw [if_neg h10] at hw
  by_cases h11 : q.1 + q.2 = 3 ∧ q.2 ≠ 0 ∧ q.2 ≠ 1 ∧ q.2 ≠ 2 ∧ q.2 ≠ 3
  · rw [if_pos h11] at hw
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h11.1, h11.2.1, h11.2.2.1, h11.2.2.2.1, h11.2.2.2.2, hw⟩)))))))))))
  rw [if_neg h11] at hw
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hw)))))))))))

/-! ### Colour `i = 0` -/

/-- The support `B_0` as a union of families. -/
def fam0 (q : Pt m) : Prop :=
  q = ptA ∨ q = ptB ∨ q = ptC ∨ q = ptY 1 ∨ q = ptY 3 ∨
    (q.2 = 2 ∧ q.1 ≠ 0 ∧ q.1 ≠ 1) ∨ (q.1 + q.2 = 3 ∧ q.1 ≠ 0 ∧ q.1 ≠ 1 ∧ q.1 ≠ 2)

section colour0

variable (h6 : 6 ≤ m)
include h6

theorem fam0_of_inB {q : Pt m} (h : inB 0 q) : fam0 q := by
  have hc := consts h6
  rcases q with ⟨a, b⟩
  rcases omega_cases (m := m) (a, b) with
    ⟨ha, hb, hw⟩ | ⟨ha, hb, hw⟩ | ⟨ha, hb, hw⟩ | ⟨ha, hb, hw⟩ | ⟨ha, hb, hw⟩ | ⟨ha, hb, hw⟩ |
    ⟨ha, hb, hw⟩ | ⟨ha, hb, hw⟩ | ⟨hb, ha0, ha1, ha2, hw⟩ | ⟨ha, hb0, hb1, hb2, hb3, hw⟩ |
    ⟨hab, hb0, hb1, hb2, hb3, hw⟩ | hw <;>
    simp only [inB, hw] at h
  · exact absurd (by decide) h
  · simp only at ha hb; subst ha; subst hb; simp [fam0, ptA, ptB, ptC, ptY, hc]
  · simp only at ha hb; subst ha; subst hb; simp [fam0, ptY]
  · simp only at ha hb; subst ha; subst hb; simp [fam0, ptC]
  · simp only at ha hb; subst ha; subst hb; simp [fam0, ptA]
  · simp only at ha hb; subst ha; subst hb; simp [fam0, ptA, ptB, ptC, ptY, hc]
  · simp only at ha hb; subst ha; subst hb; simp [fam0, ptB]
  · simp only at ha hb; subst ha; subst hb; simp [fam0, ptY]
  · simp only at hb ha0 ha1 ha2; subst hb
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ha0, ha1⟩)))))
  · exact absurd (by decide) h
  · simp only at hab hb0 hb1 hb2 hb3
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hab, ?_, ?_, ?_⟩)))))
    · exact fun h => hb3 (by linear_combination hab - h)
    · exact fun h => hb2 (by linear_combination hab - h)
    · exact fun h => hb1 (by linear_combination hab - h)
  · exact absurd (by decide) h


/-- Points of the families lie in `B_0`. -/
theorem inB_of_fam0 {q : Pt m} (h : fam0 q) : inB 0 q := by
  have hc := consts h6
  unfold inB
  rcases h with rfl | rfl | rfl | rfl | rfl | ⟨hb, ha0, ha1⟩ | ⟨hab, ha0, ha1, ha2⟩
  · rw [omega_A h6]; decide
  · rw [omega_B h6]; decide
  · rw [omega_C h6]; decide
  · rw [omega_Y1 h6]; decide
  · rw [omega_Y3 h6]; decide
  · rcases q with ⟨a, b⟩
    simp only at hb ha0 ha1
    subst hb
    by_cases ha2 : a = 2
    · subst ha2
      rw [show ((2 : ZMod m), (2 : ZMod m)) = ptX 2 from rfl, omega_X2 h6]; decide
    · rw [show ((a, (2 : ZMod m)) : Pt m) = ptX a from rfl, omega_X h6 a ha0 ha1 ha2]; decide
  · rcases q with ⟨a, b⟩
    simp only at hab ha0 ha1 ha2
    have hb : b = 3 - a := by linear_combination hab
    subst hb
    rw [show ((a, (3 : ZMod m) - a) : Pt m) = ptZ a from rfl, omega_Z h6 a ha0 ha1 ha2]; decide

/-! The local map `j_0` on the families. -/

theorem j0_A : jmap 0 (ptA : Pt m) = ptX (-1) := by
  rw [jmap, omega_A h6]; ext <;> simp [ptA, ptX, avec, p201] <;> ring

theorem j0_B : jmap 0 (ptB : Pt m) = ptZ (-1) := by
  rw [jmap, omega_B h6]; ext <;> simp [ptB, ptZ, avec, p120] <;> ring

theorem j0_C : jmap 0 (ptC : Pt m) = ptY 1 := by
  rw [jmap, omega_C h6]; ext <;> simp [ptC, ptY, avec, p201] <;> ring

theorem j0_Y1 : jmap 0 (ptY 1 : Pt m) = ptA := by
  rw [jmap, omega_Y1 h6]; ext <;> simp [ptA, ptY, avec, p120] <;> ring

theorem j0_Y3 : jmap 0 (ptY 3 : Pt m) = ptB := by
  rw [jmap, omega_Y3 h6]; ext <;> simp [ptB, ptY, avec, p201] <;> ring

theorem j0_X2 : jmap 0 (ptX 2 : Pt m) = ptY 3 := by
  rw [jmap, omega_X2 h6]; ext <;> simp [ptX, ptY, avec, p120] <;> ring

theorem j0_X (t : ZMod m) (h0 : t ≠ 0) (h1 : t ≠ 1) (h2 : t ≠ 2) :
    jmap 0 (ptX t) = ptX (t - 1) := by
  rw [jmap, omega_X h6 t h0 h1 h2]; ext <;> simp [ptX, avec, p210] <;> ring

theorem j0_Z (t : ZMod m) (h0 : t ≠ 0) (h1 : t ≠ 1) (h2 : t ≠ 2) :
    jmap 0 (ptZ t) = ptZ (t - 1) := by
  rw [jmap, omega_Z h6 t h0 h1 h2]; ext <;> simp [ptZ, avec, p102] <;> ring

end colour0

/-- The fibre partner for `ℓ_0 = a`: `A ↔ B`, `Y_1 ↔ Y_3`, `X_t ↔ Z_t`. -/
def partner0 (q : Pt m) : Pt m :=
  if q.1 = 0 then (0, 5 - q.2) else if q.1 = 1 then (1, 4 - q.2) else (q.1, 5 - q.1 - q.2)

theorem partner0_fst (q : Pt m) : (partner0 q).1 = q.1 := by
  unfold partner0
  split_ifs <;> simp [*]

section colour0b

variable (h6 : 6 ≤ m)
include h6

theorem partner0_invol (q : Pt m) : partner0 (partner0 q) = q := by
  have hc := consts h6
  rcases q with ⟨a, b⟩
  unfold partner0
  by_cases h0 : a = 0
  · subst h0; simp
  · by_cases h1 : a = 1
    · subst h1; simp [hc]
    · simp [h0, h1]
      try ring

theorem partner0_A : partner0 (ptA : Pt m) = ptB := by
  simp [partner0, ptA, ptB]; norm_num

theorem partner0_B : partner0 (ptB : Pt m) = ptA := by
  simp [partner0, ptB, ptA]; norm_num

theorem partner0_Y1 : partner0 (ptY 1 : Pt m) = ptY 3 := by
  have hc := consts h6
  simp [partner0, ptY, hc]; norm_num

theorem partner0_Y3 : partner0 (ptY 3 : Pt m) = ptY 1 := by
  have hc := consts h6
  simp [partner0, ptY, hc]; norm_num

theorem partner0_X (t : ZMod m) (h0 : t ≠ 0) (h1 : t ≠ 1) : partner0 (ptX t) = ptZ t := by
  simp [partner0, ptX, ptZ, h0, h1]; ring

theorem partner0_Z (t : ZMod m) (h0 : t ≠ 0) (h1 : t ≠ 1) : partner0 (ptZ t) = ptX t := by
  simp [partner0, ptX, ptZ, h0, h1]; ring

theorem partner0_C : partner0 (ptC : Pt m) = ptX 2 := by
  have hc := consts h6
  rw [show (ptC : Pt m) = ptZ 2 by simp [ptC, ptZ]; norm_num]
  exact partner0_Z h6 2 hc.2.2.2.1 hc.2.2.2.2.2.2.2.1

/-- The composite `N_0 ∘ j_0`. -/
def NJ0 (q : Pt m) : Pt m := partner0 (jmap 0 q)

theorem NJ0_A : NJ0 (ptA : Pt m) = ptZ (-1) := by
  rw [NJ0, j0_A h6, partner0_X h6]
  · exact fun h => (neg_cast_ne_cast (m := m) (k := 1) (c := 0) (by omega) (by omega)) (by simpa using h)
  · exact fun h => (neg_cast_ne_cast (m := m) (k := 1) (c := 1) (by omega) (by omega)) (by simpa using h)

theorem NJ0_Z (t : ZMod m) (h0 : t ≠ 0) (h1 : t ≠ 1) (h2 : t ≠ 2) : NJ0 (ptZ t) = ptX (t - 1) := by
  rw [NJ0, j0_Z h6 t h0 h1 h2, partner0_Z h6 (t - 1)]
  · exact fun h => h1 (by linear_combination h)
  · exact fun h => h2 (by linear_combination h)

theorem NJ0_X (t : ZMod m) (h0 : t ≠ 0) (h1 : t ≠ 1) (h2 : t ≠ 2) : NJ0 (ptX t) = ptZ (t - 1) := by
  rw [NJ0, j0_X h6 t h0 h1 h2, partner0_X h6 (t - 1)]
  · exact fun h => h1 (by linear_combination h)
  · exact fun h => h2 (by linear_combination h)

theorem NJ0_X2 : NJ0 (ptX 2 : Pt m) = ptY 1 := by
  rw [NJ0, j0_X2 h6, partner0_Y3 h6]

theorem NJ0_Y1 : NJ0 (ptY 1 : Pt m) = ptB := by
  rw [NJ0, j0_Y1 h6, partner0_A h6]

theorem NJ0_B : NJ0 (ptB : Pt m) = ptX (-1) := by
  rw [NJ0, j0_B h6, partner0_Z h6]
  · exact fun h => (neg_cast_ne_cast (m := m) (k := 1) (c := 0) (by omega) (by omega)) (by simpa using h)
  · exact fun h => (neg_cast_ne_cast (m := m) (k := 1) (c := 1) (by omega) (by omega)) (by simpa using h)

theorem NJ0_C : NJ0 (ptC : Pt m) = ptY 3 := by
  rw [NJ0, j0_C h6, partner0_Y1 h6]

theorem NJ0_Y3 : NJ0 (ptY 3 : Pt m) = ptA := by
  rw [NJ0, j0_Y3 h6, partner0_B h6]

end colour0b

/-! ### The `2m`-cycle of `N_0 ∘ j_0` -/

theorem neg_cast_ne_cast' {k c : ℕ} (h : ¬ m ∣ k + c) :
    -((k : ℕ) : ZMod m) ≠ ((c : ℕ) : ZMod m) := by
  intro hkc
  have h' : (((k + c : ℕ)) : ZMod m) = 0 := by
    rw [Nat.cast_add]
    linear_combination -hkc
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact h h'

/-- Position `k` on the cycle of `N_0 ∘ j_0` through `A`. -/
def pos0 (m : ℕ) (k : ℕ) : Pt m :=
  if k = 0 then ptA
  else if k ≤ m - 2 then (if k % 2 = 1 then ptZ (-(k : ZMod m)) else ptX (-(k : ZMod m)))
  else if k = m - 1 then ptY 1
  else if k = m then ptB
  else if k ≤ 2 * m - 2 then (if k % 2 = 1 then ptX (-(k : ZMod m)) else ptZ (-(k : ZMod m)))
  else ptY 3

theorem neg_cast_succ (k : ℕ) : -((k : ZMod m)) - 1 = -(((k + 1 : ℕ)) : ZMod m) := by
  push_cast
  ring

/-- The three non-membership facts needed for the generic families. -/
theorem neg_cast_not_small {k : ℕ} (hk : ¬ m ∣ k) (hk1 : ¬ m ∣ k + 1) (hk2 : ¬ m ∣ k + 2) :
    -((k : ℕ) : ZMod m) ≠ 0 ∧ -((k : ℕ) : ZMod m) ≠ 1 ∧ -((k : ℕ) : ZMod m) ≠ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using neg_cast_ne_cast' (m := m) (k := k) (c := 0) (by simpa using hk)
  · simpa using neg_cast_ne_cast' (m := m) (k := k) (c := 1) hk1
  · simpa using neg_cast_ne_cast' (m := m) (k := k) (c := 2) hk2

theorem not_dvd_of_lt_of_lt {a : ℕ} (h1 : 0 < a) (h2 : a < m) : ¬ m ∣ a :=
  fun h => absurd (Nat.le_of_dvd h1 h) (by omega)

theorem not_dvd_of_between {a : ℕ} (h1 : m < a) (h2 : a < 2 * m) : ¬ m ∣ a := by
  intro h
  have h' : m ∣ a - m := Nat.dvd_sub h (dvd_refl m)
  have := Nat.eq_zero_of_dvd_of_lt h' (by omega)
  omega

theorem cast_two_mul_sub {v : ℕ} (hv : v ≤ 2 * m) : (((2 * m - v : ℕ)) : ZMod m) = -((v : ℕ) : ZMod m) := by
  rw [Nat.cast_sub hv, Nat.cast_mul, ZMod.natCast_self]
  simp

theorem ptZ_two : (ptZ (2 : ZMod m) : Pt m) = ptC := by
  simp [ptZ, ptC]
  norm_num

section cycle0

variable (h6 : 6 ≤ m) (hm : Even m)
include h6 hm

theorem pos0_zero : pos0 m 0 = ptA := by simp [pos0]

theorem pos0_low_odd {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ m - 2) (hodd : k % 2 = 1) :
    pos0 m k = ptZ (-(k : ZMod m)) := by
  have hk0 : k ≠ 0 := by omega
  simp [pos0, hk0, h2, hodd]

theorem pos0_low_even {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ m - 2) (heven : k % 2 = 0) :
    pos0 m k = ptX (-(k : ZMod m)) := by
  have hk0 : k ≠ 0 := by omega
  simp [pos0, hk0, h2, heven]

theorem pos0_m1 : pos0 m (m - 1) = ptY 1 := by
  have h0 : m - 1 ≠ 0 := by omega
  have h2 : ¬ (m - 1 ≤ m - 2) := by omega
  simp [pos0, h0, h2]

theorem pos0_m : pos0 m m = ptB := by
  have h0 : m ≠ 0 := by omega
  have h2 : ¬ (m ≤ m - 2) := by omega
  have h3 : m ≠ m - 1 := by omega
  simp [pos0, h0, h2, h3]

theorem pos0_high_odd {k : ℕ} (h1 : m + 1 ≤ k) (h2 : k ≤ 2 * m - 2) (hodd : k % 2 = 1) :
    pos0 m k = ptX (-(k : ZMod m)) := by
  have hk0 : k ≠ 0 := by omega
  have hk2 : ¬ (k ≤ m - 2) := by omega
  have hk3 : k ≠ m - 1 := by omega
  have hk4 : k ≠ m := by omega
  simp [pos0, hk0, hk2, hk3, hk4, h2, hodd]

theorem pos0_high_even {k : ℕ} (h1 : m + 1 ≤ k) (h2 : k ≤ 2 * m - 2) (heven : k % 2 = 0) :
    pos0 m k = ptZ (-(k : ZMod m)) := by
  have hk0 : k ≠ 0 := by omega
  have hk2 : ¬ (k ≤ m - 2) := by omega
  have hk3 : k ≠ m - 1 := by omega
  have hk4 : k ≠ m := by omega
  simp [pos0, hk0, hk2, hk3, hk4, h2, heven]

theorem pos0_last : pos0 m (2 * m - 1) = ptY 3 := by
  have hk0 : 2 * m - 1 ≠ 0 := by omega
  have hk2 : ¬ (2 * m - 1 ≤ m - 2) := by omega
  have hk3 : 2 * m - 1 ≠ m - 1 := by omega
  have hk4 : 2 * m - 1 ≠ m := by omega
  have hk5 : ¬ (2 * m - 1 ≤ 2 * m - 2) := by omega
  simp [pos0, hk0, hk2, hk3, hk4, hk5]

theorem NJ0_pos0_succ {k : ℕ} (hk : k < 2 * m - 1) : NJ0 (pos0 m k) = pos0 m (k + 1) := by
  have hm' := hm
  obtain ⟨r, hr⟩ := hm'
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · rw [pos0_zero h6 hm, NJ0_A h6, pos0_low_odd h6 hm (by omega) (by omega) (by omega)]
    simp
  by_cases hlow : k ≤ m - 3
  · -- generic low region
    have hns := neg_cast_not_small (m := m) (k := k) (not_dvd_of_lt_of_lt (by omega) (by omega))
      (not_dvd_of_lt_of_lt (by omega) (by omega)) (not_dvd_of_lt_of_lt (by omega) (by omega))
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [pos0_low_even h6 hm hkpos (by omega) (by omega), NJ0_X h6 _ hns.1 hns.2.1 hns.2.2,
        pos0_low_odd h6 hm (by omega) (by omega) (by omega), neg_cast_succ]
    · rw [pos0_low_odd h6 hm hkpos (by omega) (by omega), NJ0_Z h6 _ hns.1 hns.2.1 hns.2.2,
        pos0_low_even h6 hm (by omega) (by omega) (by omega), neg_cast_succ]
  by_cases hk2 : k = m - 2
  · subst hk2
    rw [pos0_low_even h6 hm (by omega) (by omega) (by omega)]
    have : -(((m - 2 : ℕ)) : ZMod m) = 2 := by
      rw [cast_sub_self (by omega)]
      simp
    rw [this, NJ0_X2 h6, show m - 2 + 1 = m - 1 by omega, pos0_m1 h6 hm]
  by_cases hk1 : k = m - 1
  · subst hk1
    rw [pos0_m1 h6 hm, NJ0_Y1 h6, show m - 1 + 1 = m by omega, pos0_m h6 hm]
  by_cases hkm : k = m
  · subst hkm
    rw [pos0_m h6 hm, NJ0_B h6, pos0_high_odd h6 hm (by omega) (by omega) (by omega)]
    push_cast
    simp
  by_cases hhigh : k ≤ 2 * m - 3
  · have hns := neg_cast_not_small (m := m) (k := k) (not_dvd_of_between (by omega) (by omega))
      (not_dvd_of_between (by omega) (by omega)) (not_dvd_of_between (by omega) (by omega))
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [pos0_high_even h6 hm (by omega) (by omega) (by omega), NJ0_Z h6 _ hns.1 hns.2.1 hns.2.2,
        pos0_high_odd h6 hm (by omega) (by omega) (by omega), neg_cast_succ]
    · rw [pos0_high_odd h6 hm (by omega) (by omega) (by omega), NJ0_X h6 _ hns.1 hns.2.1 hns.2.2,
        pos0_high_even h6 hm (by omega) (by omega) (by omega), neg_cast_succ]
  · have hk' : k = 2 * m - 2 := by omega
    subst hk'
    rw [pos0_high_even h6 hm (by omega) (by omega) (by omega)]
    have : -(((2 * m - 2 : ℕ)) : ZMod m) = 2 := by
      rw [Nat.cast_sub (by omega), Nat.cast_mul, ZMod.natCast_self]
      simp
    rw [this, show (ptZ (2 : ZMod m)) = ptC by simp [ptZ, ptC]; norm_num, NJ0_C h6,
      show 2 * m - 2 + 1 = 2 * m - 1 by omega, pos0_last h6 hm]

theorem NJ0_pos0_wrap : NJ0 (pos0 m (2 * m - 1)) = pos0 m 0 := by
  rw [pos0_last h6 hm, NJ0_Y3 h6, pos0_zero h6 hm]

theorem NJ0_iterate {k : ℕ} (hk : k ≤ 2 * m - 1) : NJ0^[k] (ptA : Pt m) = pos0 m k := by
  induction k with
  | zero => simp [pos0_zero h6 hm]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega), NJ0_pos0_succ h6 hm (by omega)]

/-- Every point of `B_0` is on the cycle. -/
theorem exists_pos0 {q : Pt m} (hq : fam0 q) : ∃ k, k ≤ 2 * m - 1 ∧ pos0 m k = q := by
  have hm' := hm
  obtain ⟨r, hr⟩ := hm'
  rcases hq with rfl | rfl | rfl | rfl | rfl | ⟨hb, ha0, ha1⟩ | ⟨hab, ha0, ha1, ha2⟩
  · exact ⟨0, by omega, pos0_zero h6 hm⟩
  · exact ⟨m, by omega, pos0_m h6 hm⟩
  · refine ⟨2 * m - 2, by omega, ?_⟩
    rw [pos0_high_even h6 hm (by omega) (by omega) (by omega), cast_two_mul_sub (by omega),
      neg_neg]
    push_cast
    exact ptZ_two
  · exact ⟨m - 1, by omega, pos0_m1 h6 hm⟩
  · exact ⟨2 * m - 1, le_rfl, pos0_last h6 hm⟩
  · rcases q with ⟨a, b⟩
    simp only at hb ha0 ha1
    subst hb
    have hv : ((a.val : ℕ) : ZMod m) = a := ZMod.natCast_zmod_val a
    have hvlt : a.val < m := ZMod.val_lt a
    have hv0 : a.val ≠ 0 := fun h => ha0 (by rw [← hv, h]; simp)
    have hv1 : a.val ≠ 1 := fun h => ha1 (by rw [← hv, h]; simp)
    rcases Nat.even_or_odd a.val with ⟨j, hj⟩ | ⟨j, hj⟩
    · refine ⟨m - a.val, by omega, ?_⟩
      rw [pos0_low_even h6 hm (by omega) (by omega) (by omega), cast_sub_self (by omega), neg_neg,
        hv]
      rfl
    · refine ⟨2 * m - a.val, by omega, ?_⟩
      rw [pos0_high_odd h6 hm (by omega) (by omega) (by omega), cast_two_mul_sub (by omega),
        neg_neg, hv]
      rfl
  · rcases q with ⟨a, b⟩
    simp only at hab ha0 ha1 ha2
    have hb : b = 3 - a := by linear_combination hab
    subst hb
    have hv : ((a.val : ℕ) : ZMod m) = a := ZMod.natCast_zmod_val a
    have hvlt : a.val < m := ZMod.val_lt a
    have hv0 : a.val ≠ 0 := fun h => ha0 (by rw [← hv, h]; simp)
    have hv1 : a.val ≠ 1 := fun h => ha1 (by rw [← hv, h]; simp)
    have hv2 : a.val ≠ 2 := fun h => ha2 (by rw [← hv, h]; simp)
    rcases Nat.even_or_odd a.val with ⟨j, hj⟩ | ⟨j, hj⟩
    · refine ⟨2 * m - a.val, by omega, ?_⟩
      rw [pos0_high_even h6 hm (by omega) (by omega) (by omega), cast_two_mul_sub (by omega),
        neg_neg, hv]
      rfl
    · refine ⟨m - a.val, by omega, ?_⟩
      rw [pos0_low_odd h6 hm (by omega) (by omega) (by omega), cast_sub_self (by omega), neg_neg,
        hv]
      rfl

/-- The orbit of `A` under `N_0 ∘ j_0` is all of `B_0`. -/
theorem NJ0_orbit_covers {q : Pt m} (hq : inB 0 q) : ∃ k, NJ0^[k] (ptA : Pt m) = q := by
  obtain ⟨k, hk, hpos⟩ := exists_pos0 h6 hm (fam0_of_inB h6 hq)
  exact ⟨k, by rw [NJ0_iterate h6 hm hk, hpos]⟩

/-! ### Fibres of `ℓ_0` -/

theorem partner0_inB {q : Pt m} (hq : inB 0 q) : inB 0 (partner0 q) := by
  have hc := consts h6
  apply inB_of_fam0 h6
  rcases fam0_of_inB h6 hq with rfl | rfl | rfl | rfl | rfl | ⟨hb, ha0, ha1⟩ | ⟨hab, ha0, ha1, ha2⟩
  · rw [partner0_A h6]; simp [fam0]
  · rw [partner0_B h6]; simp [fam0]
  · rw [partner0_C h6]; simp [fam0, ptX, ptA, ptB, ptC, ptY, hc]
  · rw [partner0_Y1 h6]; simp [fam0]
  · rw [partner0_Y3 h6]; simp [fam0]
  · rcases q with ⟨a, b⟩
    simp only at hb ha0 ha1
    subst hb
    rw [show ((a, (2 : ZMod m)) : Pt m) = ptX a from rfl, partner0_X h6 a ha0 ha1]
    by_cases ha2 : a = 2
    · subst ha2
      rw [ptZ_two]; simp [fam0]
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp [ptZ], ha0, ha1, ha2⟩)))))
  · rcases q with ⟨a, b⟩
    simp only at hab ha0 ha1 ha2
    have hb : b = 3 - a := by linear_combination hab
    subst hb
    rw [show ((a, (3 : ZMod m) - a) : Pt m) = ptZ a from rfl, partner0_Z h6 a ha0 ha1]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ha0, ha1⟩)))))

theorem partner0_ne {q : Pt m} (hq : inB 0 q) : partner0 q ≠ q := by
  have hc := consts h6
  rcases fam0_of_inB h6 hq with rfl | rfl | rfl | rfl | rfl | ⟨hb, ha0, ha1⟩ | ⟨hab, ha0, ha1, ha2⟩
  · rw [partner0_A h6]; simp [ptA, ptB, hc]
  · rw [partner0_B h6]; simp [ptA, ptB, hc]
  · rw [partner0_C h6]; simp [ptX, ptC, hc]
  · rw [partner0_Y1 h6]; simp [ptY, hc]
  · rw [partner0_Y3 h6]; simp [ptY, hc]
  · rcases q with ⟨a, b⟩
    simp only at hb ha0 ha1
    subst hb
    rw [show ((a, (2 : ZMod m)) : Pt m) = ptX a from rfl, partner0_X h6 a ha0 ha1]
    intro h
    have := congrArg Prod.snd h
    simp [ptZ, ptX] at this
    exact ha1 (by linear_combination -this)
  · rcases q with ⟨a, b⟩
    simp only at hab ha0 ha1 ha2
    have hb : b = 3 - a := by linear_combination hab
    subst hb
    rw [show ((a, (3 : ZMod m) - a) : Pt m) = ptZ a from rfl, partner0_Z h6 a ha0 ha1]
    intro h
    have := congrArg Prod.snd h
    simp [ptZ, ptX] at this
    exact ha1 (by linear_combination this)

theorem fibre0_exists (v : ZMod m) : ∃ q : Pt m, inB 0 q ∧ q.1 = v := by
  have hc := consts h6
  by_cases h0 : v = 0
  · exact ⟨ptA, inB_of_fam0 h6 (Or.inl rfl), by simp [ptA, h0]⟩
  by_cases h1 : v = 1
  · exact ⟨ptY 1, inB_of_fam0 h6 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), by simp [ptY, h1]⟩
  · exact ⟨ptX v, inB_of_fam0 h6 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h0, h1⟩)))))),
      rfl⟩

/-- The families grouped by first coordinate. -/
theorem fam0_classes {q : Pt m} (hq : fam0 q) :
    (q.1 = 0 ∧ (q = ptA ∨ q = ptB)) ∨ (q.1 = 1 ∧ (q = ptY 1 ∨ q = ptY 3)) ∨
    (q.1 = 2 ∧ (q = ptC ∨ q = ptX 2)) ∨
    (q.1 ≠ 0 ∧ q.1 ≠ 1 ∧ q.1 ≠ 2 ∧ (q = ptX q.1 ∨ q = ptZ q.1)) := by
  rcases hq with rfl | rfl | rfl | rfl | rfl | ⟨hb, ha0, ha1⟩ | ⟨hab, ha0, ha1, ha2⟩
  · exact Or.inl ⟨rfl, Or.inl rfl⟩
  · exact Or.inl ⟨rfl, Or.inr rfl⟩
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩))
  · exact Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)
  · exact Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)
  · rcases q with ⟨a, b⟩
    simp only at hb ha0 ha1
    subst hb
    by_cases ha2 : a = 2
    · subst ha2
      exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ha0, ha1, ha2, Or.inl rfl⟩))
  · rcases q with ⟨a, b⟩
    simp only at hab ha0 ha1 ha2
    have hb : b = 3 - a := by linear_combination hab
    subst hb
    exact Or.inr (Or.inr (Or.inr ⟨ha0, ha1, ha2, Or.inr rfl⟩))

theorem fam0_fst_zero {q : Pt m} (hq : fam0 q) (h : q.1 = 0) : q = ptA ∨ q = ptB := by
  have hc := consts h6
  rcases fam0_classes h6 hm hq with ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha0, ha1, ha2, hq1⟩
  · exact hq1
  · exact absurd (ha.symm.trans h) hc.2.1
  · exact absurd (ha.symm.trans h) hc.2.2.2.1
  · exact absurd h ha0

theorem fam0_fst_one {q : Pt m} (hq : fam0 q) (h : q.1 = 1) : q = ptY 1 ∨ q = ptY 3 := by
  have hc := consts h6
  rcases fam0_classes h6 hm hq with ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha0, ha1, ha2, hq1⟩
  · exact absurd (ha.symm.trans h) hc.1
  · exact hq1
  · exact absurd (ha.symm.trans h) hc.2.2.2.2.2.2.2.1
  · exact absurd h ha1

theorem fam0_fst_two {q : Pt m} (hq : fam0 q) (h : q.1 = 2) : q = ptC ∨ q = ptX 2 := by
  have hc := consts h6
  rcases fam0_classes h6 hm hq with ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha0, ha1, ha2, hq1⟩
  · exact absurd (ha.symm.trans h) hc.2.2.1
  · exact absurd (ha.symm.trans h) hc.2.2.2.2.2.2.1
  · exact hq1
  · exact absurd h ha2

theorem fam0_fst_other {q : Pt m} (hq : fam0 q) (h0 : q.1 ≠ 0) (h1 : q.1 ≠ 1) (h2 : q.1 ≠ 2) :
    q = ptX q.1 ∨ q = ptZ q.1 := by
  rcases fam0_classes h6 hm hq with ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha0, ha1, ha2, hq1⟩
  · exact absurd ha h0
  · exact absurd ha h1
  · exact absurd ha h2
  · exact hq1

theorem fibre0_unique {q q' : Pt m} (hq : inB 0 q) (hq' : inB 0 q') (h : q'.1 = q.1) :
    q' = q ∨ q' = partner0 q := by
  have hc := consts h6
  have hf := fam0_of_inB h6 hq
  have hf' := fam0_of_inB h6 hq'
  rcases fam0_classes h6 hm hf with ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha0, ha1, ha2, hq1⟩
  · rcases fam0_fst_zero h6 hm hf' (h.trans ha) with rfl | rfl <;> rcases hq1 with rfl | rfl <;>
      simp [partner0_A h6, partner0_B h6]
  · rcases fam0_fst_one h6 hm hf' (h.trans ha) with rfl | rfl <;> rcases hq1 with rfl | rfl <;>
      simp [partner0_Y1 h6, partner0_Y3 h6]
  · rcases fam0_fst_two h6 hm hf' (h.trans ha) with rfl | rfl <;> rcases hq1 with rfl | rfl <;>
      simp [partner0_C h6, partner0_X h6 2 hc.2.2.2.1 hc.2.2.2.2.2.2.2.1, ptZ_two]
  · have h0' : q'.1 ≠ 0 := by rw [h]; exact ha0
    have h1' : q'.1 ≠ 1 := by rw [h]; exact ha1
    have h2' : q'.1 ≠ 2 := by rw [h]; exact ha2
    rcases fam0_fst_other h6 hm hf' h0' h1' h2' with hq2 | hq2 <;>
      rcases hq1 with hq1 | hq1 <;> rw [h] at hq2
    · left; rw [hq2, ← hq1]
    · right
      rw [hq2]
      conv_rhs => rw [hq1]
      rw [partner0_Z h6 _ ha0 ha1]
    · right
      rw [hq2]
      conv_rhs => rw [hq1]
      rw [partner0_X h6 _ ha0 ha1]
    · left; rw [hq2, ← hq1]

/-- `j_0` maps `B_0` into itself. -/
theorem jmap0_inB {q : Pt m} (hq : inB 0 q) : inB 0 (jmap 0 q) := by
  have hc := consts h6
  apply inB_of_fam0 h6
  have hn1 := neg_cast_not_small (m := m) (k := 1) (not_dvd_of_lt_of_lt (by omega) (by omega))
    (not_dvd_of_lt_of_lt (by omega) (by omega)) (not_dvd_of_lt_of_lt (by omega) (by omega))
  simp only [Nat.cast_one] at hn1
  rcases fam0_of_inB h6 hq with rfl | rfl | rfl | rfl | rfl | ⟨hb, ha0, ha1⟩ | ⟨hab, ha0, ha1, ha2⟩
  · rw [j0_A h6]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hn1.1, hn1.2.1⟩)))))
  · rw [j0_B h6]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨by simp [ptZ], hn1.1, hn1.2.1, hn1.2.2⟩)))))
  · rw [j0_C h6]; simp [fam0]
  · rw [j0_Y1 h6]; simp [fam0]
  · rw [j0_Y3 h6]; simp [fam0]
  · rcases q with ⟨a, b⟩
    simp only at hb ha0 ha1
    subst hb
    by_cases ha2 : a = 2
    · subst ha2
      rw [show ((2 : ZMod m), (2 : ZMod m)) = ptX 2 from rfl, j0_X2 h6]; simp [fam0]
    · rw [show ((a, (2 : ZMod m)) : Pt m) = ptX a from rfl, j0_X h6 a ha0 ha1 ha2]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,
        fun h => ha1 (by simp [ptX] at h; linear_combination h),
        fun h => ha2 (by simp [ptX] at h; linear_combination h)⟩)))))
  · rcases q with ⟨a, b⟩
    simp only at hab ha0 ha1 ha2
    have hb : b = 3 - a := by linear_combination hab
    subst hb
    rw [show ((a, (3 : ZMod m) - a) : Pt m) = ptZ a from rfl, j0_Z h6 a ha0 ha1 ha2]
    by_cases ha3 : a = 3
    · subst ha3
      rw [show (3 : ZMod m) - 1 = 2 by norm_num, ptZ_two]; simp [fam0]
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp [ptZ],
        fun h => ha1 (by simp [ptZ] at h; linear_combination h),
        fun h => ha2 (by simp [ptZ] at h; linear_combination h),
        fun h => ha3 (by simp [ptZ] at h; linear_combination h)⟩)))))

theorem NJ0_inB {q : Pt m} (hq : inB 0 q) : inB 0 (NJ0 q) :=
  partner0_inB h6 hm (jmap0_inB h6 hm hq)

end cycle0

end D5
end TorusEven
