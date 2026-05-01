import D7Odd.LocalRows

namespace D7Odd

def C0Pred (m : Nat) (w : Vec7 m) : Prop :=
  w 0 = 0 ∧ w 2 = 0 ∧ w 4 = 0 ∧ w 6 = 0 ∧ w 5 ≠ 0

def C5Pred (m : Nat) (w : Vec7 m) : Prop :=
  w 0 = 0 ∧ w 2 = 0 ∧ w 4 = 0 ∧ w 5 = 0 ∧ w 3 ≠ 0

noncomputable def dC0 (m : Nat) (w : Vec7 m) : Fin 7 := by
  classical
  exact if C0Pred m w then 3 else if C5Pred m w then 6 else 1

noncomputable def PC (m : Nat) (w : Vec7 m) : Vec7 m :=
  w + q7 m (dC0 m w)

def C0Target (m : Nat) (y : Vec7 m) : Prop :=
  y 0 = 0 ∧ y 2 = 0 ∧ y 4 = 0 ∧ y 6 = -1 ∧ y 5 ≠ 0

def C5Target (m : Nat) (y : Vec7 m) : Prop :=
  y 0 = 0 ∧ y 2 = 0 ∧ y 4 = 0 ∧ y 5 = 0 ∧ y 3 ≠ 0

theorem add_one_eq_zero_iff_eq_neg_one {m : Nat} (x : ZMod m) :
    x + 1 = 0 ↔ x = -1 := by
  constructor
  · intro h
    calc
      x = x + 1 - 1 := by ring
      _ = 0 - 1 := by rw [h]
      _ = -1 := by ring
  · intro h
    rw [h]
    ring

theorem C0Pred_sub_q3_iff (m : Nat) (y : Vec7 m) :
    C0Pred m (y - q7 m 3) ↔ C0Target m y := by
  simp [C0Pred, C0Target, q7, e7, sub_eq_add_neg, add_one_eq_zero_iff_eq_neg_one]

theorem C5Pred_sub_q6_iff (m : Nat) (y : Vec7 m) :
    C5Pred m (y - q7 m 6) ↔ C5Target m y := by
  simp [C5Pred, C5Target, q7]

theorem C0Pred_sub_q1_iff (m : Nat) (y : Vec7 m) :
    C0Pred m (y - q7 m 1) ↔ C0Target m y := by
  simp [C0Pred, C0Target, q7, e7, sub_eq_add_neg, add_one_eq_zero_iff_eq_neg_one]

theorem C5Pred_sub_q1_iff (m : Nat) (y : Vec7 m) :
    C5Pred m (y - q7 m 1) ↔ C5Target m y := by
  simp [C5Pred, C5Target, q7, e7]

theorem C_targets_disjoint {m : Nat} {y : Vec7 m}
    (h0 : C0Target m y) (h5 : C5Target m y) : False :=
  h0.2.2.2.2 h5.2.2.2.1

theorem dC0_eq_three_or_six_or_one (m : Nat) (w : Vec7 m) :
    dC0 m w = 3 ∨ dC0 m w = 6 ∨ dC0 m w = 1 := by
  classical
  by_cases h0 : C0Pred m w
  · simp [dC0, h0]
  · by_cases h5 : C5Pred m w
    · simp [dC0, h0, h5]
    · simp [dC0, h0, h5]

theorem dC0_value_of_eq {m : Nat} {w : Vec7 m} {i : Fin 7}
    (hi : dC0 m w = i) : i = 3 ∨ i = 6 ∨ i = 1 := by
  rcases dC0_eq_three_or_six_or_one m w with h3 | h6 | h1
  · exact Or.inl (hi.symm.trans h3)
  · exact Or.inr (Or.inl (hi.symm.trans h6))
  · exact Or.inr (Or.inr (hi.symm.trans h1))

private theorem impossible_dC0_value {m : Nat} {w : Vec7 m} {i : Fin 7}
    (hi : dC0 m w = i) (h3 : i ≠ 3) (h6 : i ≠ 6) (h1 : i ≠ 1) :
    False := by
  rcases dC0_value_of_eq hi with hi3 | hi6 | hi1
  · exact h3 hi3
  · exact h6 hi6
  · exact h1 hi1

theorem dC0_ne_three_of_not_C0 {m : Nat} {w : Vec7 m} (hnotC0 : ¬C0Pred m w) :
    dC0 m w ≠ 3 := by
  classical
  by_cases hC5 : C5Pred m w
  · simp [dC0, hnotC0, hC5]
  · simp [dC0, hnotC0, hC5]

theorem dC0_ne_six_of_not_C5 {m : Nat} {w : Vec7 m} (hnotC5 : ¬C5Pred m w) :
    dC0 m w ≠ 6 := by
  classical
  by_cases hC0 : C0Pred m w
  · simp [dC0, hC0]
  · simp [dC0, hC0, hnotC5]

theorem dC0_q3_of_C0Target (m : Nat) (y : Vec7 m) (h : C0Target m y) :
    dC0 m (y - q7 m 3) = 3 := by
  classical
  have hC0 : C0Pred m (y - q7 m 3) := (C0Pred_sub_q3_iff m y).2 h
  simp [dC0, hC0]

theorem dC0_q1_of_C0Target (m : Nat) (y : Vec7 m) (h : C0Target m y) :
    dC0 m (y - q7 m 1) = 3 := by
  classical
  have hC0 : C0Pred m (y - q7 m 1) := (C0Pred_sub_q1_iff m y).2 h
  simp [dC0, hC0]

theorem dC0_q6_of_C0Target (m : Nat) [NeZero m] (hm : 5 ≤ m) (y : Vec7 m)
    (h : C0Target m y) :
    dC0 m (y - q7 m 6) = 1 := by
  classical
  have hnotC0 : ¬C0Pred m (y - q7 m 6) := by
    intro hC0
    have hy6zero : y 6 = 0 := by
      simpa [q7] using hC0.2.2.2.1
    exact zmod_neg_one_ne_zero_of_ge5 (m := m) hm (h.2.2.2.1.symm.trans hy6zero)
  have hnotC5 : ¬C5Pred m (y - q7 m 6) := by
    intro hC5
    have hy5zero : y 5 = 0 := by
      simpa [q7] using hC5.2.2.2.1
    exact h.2.2.2.2 hy5zero
  simp [dC0, hnotC0, hnotC5]

theorem dC0_q6_of_C5Target (m : Nat) (y : Vec7 m) (h : C5Target m y) :
    dC0 m (y - q7 m 6) = 6 := by
  classical
  have hC5 : C5Pred m (y - q7 m 6) := (C5Pred_sub_q6_iff m y).2 h
  have hnotC0 : ¬C0Pred m (y - q7 m 6) := by
    intro hC0
    have hy5ne : y 5 ≠ 0 := by
      simpa [q7, e7] using hC0.2.2.2.2
    exact hy5ne h.2.2.2.1
  simp [dC0, hnotC0, hC5]

theorem dC0_q1_of_C5Target (m : Nat) (y : Vec7 m) (h : C5Target m y) :
    dC0 m (y - q7 m 1) = 6 := by
  classical
  have hC5 : C5Pred m (y - q7 m 1) := (C5Pred_sub_q1_iff m y).2 h
  have hnotC0 : ¬C0Pred m (y - q7 m 1) := by
    intro hC0
    exact C_targets_disjoint ((C0Pred_sub_q1_iff m y).1 hC0) h
  simp [dC0, hnotC0, hC5]

theorem dC0_q1_of_default (m : Nat) (y : Vec7 m)
    (h0 : ¬C0Target m y) (h5 : ¬C5Target m y) :
    dC0 m (y - q7 m 1) = 1 := by
  classical
  have hnotC0 : ¬C0Pred m (y - q7 m 1) := fun h => h0 ((C0Pred_sub_q1_iff m y).1 h)
  have hnotC5 : ¬C5Pred m (y - q7 m 1) := fun h => h5 ((C5Pred_sub_q1_iff m y).1 h)
  simp [dC0, hnotC0, hnotC5]

theorem C_phase_unique_predecessor (m : Nat) [NeZero m] (hm : 5 ≤ m) (y : Vec7 m) :
    ∃! i : Fin 7, dC0 m (y - q7 m i) = i := by
  classical
  by_cases h0 : C0Target m y
  · refine ⟨3, dC0_q3_of_C0Target m y h0, ?_⟩
    intro i hi
    fin_cases i
    · exact False.elim <| impossible_dC0_value hi (by decide) (by decide) (by decide)
    · exfalso
      have hd := dC0_q1_of_C0Target m y h0
      exact (by decide : (3 : Fin 7) ≠ 1) (hd.symm.trans hi)
    · exact False.elim <| impossible_dC0_value hi (by decide) (by decide) (by decide)
    · rfl
    · exact False.elim <| impossible_dC0_value hi (by decide) (by decide) (by decide)
    · exact False.elim <| impossible_dC0_value hi (by decide) (by decide) (by decide)
    · exfalso
      have hd := dC0_q6_of_C0Target m hm y h0
      exact (by decide : (1 : Fin 7) ≠ 6) (hd.symm.trans hi)
  · by_cases h5 : C5Target m y
    · refine ⟨6, dC0_q6_of_C5Target m y h5, ?_⟩
      intro i hi
      fin_cases i
      · exact False.elim <| impossible_dC0_value hi (by decide) (by decide) (by decide)
      · exfalso
        have hd := dC0_q1_of_C5Target m y h5
        exact (by decide : (6 : Fin 7) ≠ 1) (hd.symm.trans hi)
      · exact False.elim <| impossible_dC0_value hi (by decide) (by decide) (by decide)
      · exfalso
        have hnotC0 : ¬C0Pred m (y - q7 m 3) := by
          intro hC0
          exact C_targets_disjoint ((C0Pred_sub_q3_iff m y).1 hC0) h5
        exact dC0_ne_three_of_not_C0 hnotC0 hi
      · exact False.elim <| impossible_dC0_value hi (by decide) (by decide) (by decide)
      · exact False.elim <| impossible_dC0_value hi (by decide) (by decide) (by decide)
      · rfl
    · refine ⟨1, dC0_q1_of_default m y h0 h5, ?_⟩
      intro i hi
      fin_cases i
      · exact False.elim <| impossible_dC0_value hi (by decide) (by decide) (by decide)
      · rfl
      · exact False.elim <| impossible_dC0_value hi (by decide) (by decide) (by decide)
      · exfalso
        have hnotC0 : ¬C0Pred m (y - q7 m 3) := fun h => h0 ((C0Pred_sub_q3_iff m y).1 h)
        exact dC0_ne_three_of_not_C0 hnotC0 hi
      · exact False.elim <| impossible_dC0_value hi (by decide) (by decide) (by decide)
      · exact False.elim <| impossible_dC0_value hi (by decide) (by decide) (by decide)
      · exfalso
        have hnotC5 : ¬C5Pred m (y - q7 m 6) := fun h => h5 ((C5Pred_sub_q6_iff m y).1 h)
        exact dC0_ne_six_of_not_C5 hnotC5 hi

theorem C_phase_matching_color0 (m : Nat) [NeZero m] (hm : 5 ≤ m) (y : Vec7 m) :
    ∃! i : Fin 7, dC0 m (y - q7 m i) = i :=
  C_phase_unique_predecessor m hm y

def S0Pred (m : Nat) (w : Vec7 m) : Prop :=
  w 0 = 0 ∧ w 4 = 0 ∧ w 6 = 0 ∧ w 2 = -1

def S3Pred (m : Nat) (w : Vec7 m) : Prop :=
  w 3 = 0 ∧ w 0 = 0 ∧ w 2 = 0 ∧ w 5 = -1

noncomputable def dS0 (m : Nat) (w : Vec7 m) : Fin 7 := by
  classical
  exact if S0Pred m w then 5 else if S3Pred m w then 4 else 1

noncomputable def PS (m : Nat) (w : Vec7 m) : Vec7 m :=
  w + q7 m (dS0 m w)

def S0Target (m : Nat) (y : Vec7 m) : Prop :=
  y 0 = 0 ∧ y 4 = 0 ∧ y 6 = -1 ∧ y 2 = -1

def S3Target (m : Nat) (y : Vec7 m) : Prop :=
  y 3 = 0 ∧ y 0 = 0 ∧ y 2 = 0 ∧ y 5 = -1

theorem S0Pred_sub_q5_iff (m : Nat) (y : Vec7 m) :
    S0Pred m (y - q7 m 5) ↔ S0Target m y := by
  simp [S0Pred, S0Target, q7, e7, sub_eq_add_neg, add_one_eq_zero_iff_eq_neg_one]

theorem S3Pred_sub_q4_iff (m : Nat) (y : Vec7 m) :
    S3Pred m (y - q7 m 4) ↔ S3Target m y := by
  simp [S3Pred, S3Target, q7, e7]

theorem S0Pred_sub_q1_iff (m : Nat) (y : Vec7 m) :
    S0Pred m (y - q7 m 1) ↔ S0Target m y := by
  simp [S0Pred, S0Target, q7, e7, sub_eq_add_neg, add_one_eq_zero_iff_eq_neg_one]

theorem S3Pred_sub_q1_iff (m : Nat) (y : Vec7 m) :
    S3Pred m (y - q7 m 1) ↔ S3Target m y := by
  simp [S3Pred, S3Target, q7, e7]

theorem S_targets_disjoint {m : Nat} [NeZero m] (hm : 5 ≤ m) {y : Vec7 m}
    (h0 : S0Target m y) (h3 : S3Target m y) : False :=
  zmod_neg_one_ne_zero_of_ge5 (m := m) hm (h0.2.2.2.symm.trans h3.2.2.1)

theorem dS0_eq_five_or_four_or_one (m : Nat) (w : Vec7 m) :
    dS0 m w = 5 ∨ dS0 m w = 4 ∨ dS0 m w = 1 := by
  classical
  by_cases h0 : S0Pred m w
  · simp [dS0, h0]
  · by_cases h3 : S3Pred m w
    · simp [dS0, h0, h3]
    · simp [dS0, h0, h3]

theorem dS0_value_of_eq {m : Nat} {w : Vec7 m} {i : Fin 7}
    (hi : dS0 m w = i) : i = 5 ∨ i = 4 ∨ i = 1 := by
  rcases dS0_eq_five_or_four_or_one m w with h5 | h4 | h1
  · exact Or.inl (hi.symm.trans h5)
  · exact Or.inr (Or.inl (hi.symm.trans h4))
  · exact Or.inr (Or.inr (hi.symm.trans h1))

private theorem impossible_dS0_value {m : Nat} {w : Vec7 m} {i : Fin 7}
    (hi : dS0 m w = i) (h5 : i ≠ 5) (h4 : i ≠ 4) (h1 : i ≠ 1) :
    False := by
  rcases dS0_value_of_eq hi with hi5 | hi4 | hi1
  · exact h5 hi5
  · exact h4 hi4
  · exact h1 hi1

theorem dS0_ne_five_of_not_S0 {m : Nat} {w : Vec7 m} (hnotS0 : ¬S0Pred m w) :
    dS0 m w ≠ 5 := by
  classical
  by_cases hS3 : S3Pred m w
  · simp [dS0, hnotS0, hS3]
  · simp [dS0, hnotS0, hS3]

theorem dS0_ne_four_of_not_S3 {m : Nat} {w : Vec7 m} (hnotS3 : ¬S3Pred m w) :
    dS0 m w ≠ 4 := by
  classical
  by_cases hS0 : S0Pred m w
  · simp [dS0, hS0]
  · simp [dS0, hS0, hnotS3]

theorem dS0_q5_of_S0Target (m : Nat) (y : Vec7 m) (h : S0Target m y) :
    dS0 m (y - q7 m 5) = 5 := by
  classical
  have hS0 : S0Pred m (y - q7 m 5) := (S0Pred_sub_q5_iff m y).2 h
  simp [dS0, hS0]

theorem dS0_q1_of_S0Target (m : Nat) (y : Vec7 m) (h : S0Target m y) :
    dS0 m (y - q7 m 1) = 5 := by
  classical
  have hS0 : S0Pred m (y - q7 m 1) := (S0Pred_sub_q1_iff m y).2 h
  simp [dS0, hS0]

theorem dS0_q4_of_S3Target (m : Nat) [NeZero m] (hm : 5 ≤ m) (y : Vec7 m)
    (h : S3Target m y) :
    dS0 m (y - q7 m 4) = 4 := by
  classical
  have hS3 : S3Pred m (y - q7 m 4) := (S3Pred_sub_q4_iff m y).2 h
  have hnotS0 : ¬S0Pred m (y - q7 m 4) := by
    intro hS0
    have hy2neg : y 2 = -1 := by
      simpa [q7, e7] using hS0.2.2.2
    exact zmod_neg_one_ne_zero_of_ge5 (m := m) hm (hy2neg.symm.trans h.2.2.1)
  simp [dS0, hnotS0, hS3]

theorem dS0_q1_of_S3Target (m : Nat) [NeZero m] (hm : 5 ≤ m) (y : Vec7 m)
    (h : S3Target m y) :
    dS0 m (y - q7 m 1) = 4 := by
  classical
  have hS3 : S3Pred m (y - q7 m 1) := (S3Pred_sub_q1_iff m y).2 h
  have hnotS0 : ¬S0Pred m (y - q7 m 1) := by
    intro hS0
    exact S_targets_disjoint hm ((S0Pred_sub_q1_iff m y).1 hS0) h
  simp [dS0, hnotS0, hS3]

theorem dS0_q1_of_default (m : Nat) (y : Vec7 m)
    (h0 : ¬S0Target m y) (h3 : ¬S3Target m y) :
    dS0 m (y - q7 m 1) = 1 := by
  classical
  have hnotS0 : ¬S0Pred m (y - q7 m 1) := fun h => h0 ((S0Pred_sub_q1_iff m y).1 h)
  have hnotS3 : ¬S3Pred m (y - q7 m 1) := fun h => h3 ((S3Pred_sub_q1_iff m y).1 h)
  simp [dS0, hnotS0, hnotS3]

theorem SB_phase_unique_predecessor (m : Nat) [NeZero m] (hm : 5 ≤ m) (y : Vec7 m) :
    ∃! i : Fin 7, dS0 m (y - q7 m i) = i := by
  classical
  by_cases h0 : S0Target m y
  · refine ⟨5, dS0_q5_of_S0Target m y h0, ?_⟩
    intro i hi
    fin_cases i
    · exact False.elim <| impossible_dS0_value hi (by decide) (by decide) (by decide)
    · exfalso
      have hd := dS0_q1_of_S0Target m y h0
      exact (by decide : (5 : Fin 7) ≠ 1) (hd.symm.trans hi)
    · exact False.elim <| impossible_dS0_value hi (by decide) (by decide) (by decide)
    · exact False.elim <| impossible_dS0_value hi (by decide) (by decide) (by decide)
    · exfalso
      have hnotS3 : ¬S3Pred m (y - q7 m 4) := by
        intro hS3
        exact S_targets_disjoint hm h0 ((S3Pred_sub_q4_iff m y).1 hS3)
      exact dS0_ne_four_of_not_S3 hnotS3 hi
    · rfl
    · exact False.elim <| impossible_dS0_value hi (by decide) (by decide) (by decide)
  · by_cases h3 : S3Target m y
    · refine ⟨4, dS0_q4_of_S3Target m hm y h3, ?_⟩
      intro i hi
      fin_cases i
      · exact False.elim <| impossible_dS0_value hi (by decide) (by decide) (by decide)
      · exfalso
        have hd := dS0_q1_of_S3Target m hm y h3
        exact (by decide : (4 : Fin 7) ≠ 1) (hd.symm.trans hi)
      · exact False.elim <| impossible_dS0_value hi (by decide) (by decide) (by decide)
      · exact False.elim <| impossible_dS0_value hi (by decide) (by decide) (by decide)
      · rfl
      · exfalso
        have hnotS0 : ¬S0Pred m (y - q7 m 5) := by
          intro hS0
          exact S_targets_disjoint hm ((S0Pred_sub_q5_iff m y).1 hS0) h3
        exact dS0_ne_five_of_not_S0 hnotS0 hi
      · exact False.elim <| impossible_dS0_value hi (by decide) (by decide) (by decide)
    · refine ⟨1, dS0_q1_of_default m y h0 h3, ?_⟩
      intro i hi
      fin_cases i
      · exact False.elim <| impossible_dS0_value hi (by decide) (by decide) (by decide)
      · rfl
      · exact False.elim <| impossible_dS0_value hi (by decide) (by decide) (by decide)
      · exact False.elim <| impossible_dS0_value hi (by decide) (by decide) (by decide)
      · exfalso
        have hnotS3 : ¬S3Pred m (y - q7 m 4) := fun h => h3 ((S3Pred_sub_q4_iff m y).1 h)
        exact dS0_ne_four_of_not_S3 hnotS3 hi
      · exfalso
        have hnotS0 : ¬S0Pred m (y - q7 m 5) := fun h => h0 ((S0Pred_sub_q5_iff m y).1 h)
        exact dS0_ne_five_of_not_S0 hnotS0 hi
      · exact False.elim <| impossible_dS0_value hi (by decide) (by decide) (by decide)

theorem SB_phase_matching_color0 (m : Nat) [NeZero m] (hm : 5 ≤ m) (y : Vec7 m) :
    ∃! i : Fin 7, dS0 m (y - q7 m i) = i :=
  SB_phase_unique_predecessor m hm y

end D7Odd
