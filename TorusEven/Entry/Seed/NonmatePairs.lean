-- STATUS: main-path
import TorusEven.Entry.Seed.Residual

namespace TorusEven.Entry.Seed

def nonmateIndex (p t : ℕ) : ℕ :=
  if p = 3 then 4 + t else
  if p % 2 = 0 then (if t < p - 2 then t + 2 else t + 4) else
  if t = 0 then 1 else if t = 1 then p + 2 else if t < p - 1 then t + 1 else t + 4

variable (p : ℕ) (hp : 2 ≤ p)

def nonmateOrder : Fin (2 * (p - 2)) ↪ Shell.Color p where
  toFun t := ⟨nonmateIndex p t.val, by
    have ht := t.isLt
    unfold nonmateIndex
    split_ifs <;> omega⟩
  inj' s t h := by
    have hs := s.isLt
    have ht := t.isLt
    have hv := congrArg Fin.val h
    change nonmateIndex p s.val = nonmateIndex p t.val at hv
    apply Fin.ext
    unfold nonmateIndex at hv
    split_ifs at hv <;> omega

theorem nonmateOrder_mem (t : Fin (2 * (p - 2))) : nonmateOrder p hp t ∈ nonmates p hp := by
  rw [mem_nonmates_iff]
  change (if p = 3 then nonmateIndex p t.val = 4 ∨ nonmateIndex p t.val = 5 else
    if p % 2 = 0 then (2 ≤ nonmateIndex p t.val ∧ nonmateIndex p t.val < p) ∨
      p + 2 ≤ nonmateIndex p t.val else nonmateIndex p t.val = 1 ∨
      (3 ≤ nonmateIndex p t.val ∧ nonmateIndex p t.val < p) ∨ p + 2 ≤ nonmateIndex p t.val)
  have ht := t.isLt
  unfold nonmateIndex
  split_ifs <;> omega

theorem nonmateOrder_surjective (c : nonmates p hp) : ∃ t, nonmateOrder p hp t = c.val := by
  have hc := c.val.isLt
  have ht := (mem_nonmates_iff p hp c.val).mp c.property
  suffices ∃ t, t < 2 * (p - 2) ∧ nonmateIndex p t = c.val.val by
    obtain ⟨t, hlt, he⟩ := this
    exact ⟨⟨t, hlt⟩, Fin.ext he⟩
  by_cases h3 : p = 3
  · refine ⟨c.val.val - 4, ?_, ?_⟩ <;> simp only [h3, if_true] at ht
    · omega
    · simp only [nonmateIndex, h3, if_true]
      omega
  · by_cases he : p % 2 = 0
    · simp only [h3, if_false, he, if_true] at ht
      rcases ht with ha | hb
      · refine ⟨c.val.val - 2, by omega, ?_⟩
        simp only [nonmateIndex, h3, if_false, he, if_true,
          if_pos (by omega : c.val.val - 2 < p - 2)]
        omega
      · refine ⟨c.val.val - 4, by omega, ?_⟩
        simp only [nonmateIndex, h3, if_false, he, if_true,
          if_neg (by omega : ¬c.val.val - 4 < p - 2)]
        omega
    · simp only [h3, if_false, he] at ht
      rcases ht with ha | ha | hb
      · exact ⟨0, by omega, by simp [nonmateIndex, h3, he, ha]⟩
      · refine ⟨c.val.val - 1, by omega, ?_⟩
        simp only [nonmateIndex, h3, he, if_false, if_neg (by omega : c.val.val - 1 ≠ 0),
          if_neg (by omega : c.val.val - 1 ≠ 1), if_pos (by omega : c.val.val - 1 < p - 1)]
        omega
      · by_cases hb2 : c.val.val = p + 2
        · exact ⟨1, by omega, by simp [nonmateIndex, h3, he, hb2]⟩
        · refine ⟨c.val.val - 4, by omega, ?_⟩
          simp only [nonmateIndex, h3, he, if_false, if_neg (by omega : c.val.val - 4 ≠ 0),
            if_neg (by omega : c.val.val - 4 ≠ 1), if_neg (by omega : ¬c.val.val - 4 < p - 1)]
          omega

noncomputable def nonmateEquiv : Fin (2 * (p - 2)) ≃ nonmates p hp :=
  Equiv.ofBijective (fun t => ⟨nonmateOrder p hp t, nonmateOrder_mem p hp t⟩)
    ⟨fun _ _ h => (nonmateOrder p hp).injective (congrArg Subtype.val h), fun c => by
      obtain ⟨t, ht⟩ := nonmateOrder_surjective p hp c
      exact ⟨t, Subtype.ext ht⟩⟩

noncomputable def nonmatePairs : Fin (p - 2) × Bool ≃ nonmates p hp :=
  (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans
    (finProdFinEquiv.trans ((finCongr (Nat.mul_comm _ _)).trans (nonmateEquiv p hp)))

theorem nonmatePairs_val (i : Fin (p - 2)) (b : Bool) :
    (nonmatePairs p hp (i, b)).val.val = nonmateIndex p (2 * i.val + if b then 1 else 0) := by
  change nonmateIndex p ((finTwoEquiv.symm b).val + 2 * i.val) = _
  cases b <;> simp [finTwoEquiv, Nat.add_comm]

end TorusEven.Entry.Seed
