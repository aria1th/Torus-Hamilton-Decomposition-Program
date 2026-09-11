-- STATUS: main-path
import TorusEven.Collar.PinnedRows

namespace TorusEven.Collar

variable {Ω R : Type*} [DecidableEq Ω] [DecidableEq R]

def switchedRow (a b : Ω) (event t : R) (F : Finset Ω) : Finset Ω :=
  insert (if t = event then a else b) F

theorem switchedRow_subset (a b : Ω) (event t : R) {F A : Finset Ω}
    (ha : a ∈ A) (hb : b ∈ A) (hF : F ⊆ A) : switchedRow a b event t F ⊆ A := by
  apply Finset.insert_subset_iff.mpr ⟨?_, hF⟩
  split_ifs <;> assumption

theorem card_switchedRow (a b : Ω) (event t : R) (F : Finset Ω)
    (ha : a ∉ F) (hb : b ∉ F) : (switchedRow a b event t F).card = F.card + 1 := by
  unfold switchedRow
  split_ifs <;> simp [ha, hb]

theorem complement_switchedRow (a b : Ω) (event t : R) (A F : Finset Ω)
    (hab : a ≠ b) (ha : a ∉ A) (hb : b ∉ A) (hF : F ⊆ A) :
    insert a (insert b A) \ switchedRow a b event t F =
      switchedRow b a event t (A \ F) := by
  have hFa : a ∉ F := fun h => ha (hF h)
  have hFb : b ∉ F := fun h => hb (hF h)
  ext x
  by_cases ht : t = event <;> by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    simp_all [switchedRow]

theorem coherent_switchedRow (a b : Ω) (event base : R) (J : R → Finset Ω)
    (hne : base ≠ event) (hmeet : (J event ∩ J base).Nonempty) :
    Incidence.Coherent (fun t => switchedRow a b event t (J t)) := by
  have h (t : R) : ∃ x, x ∈ switchedRow a b event t (J t) ∧
      x ∈ switchedRow a b event base (J base) := by
    by_cases ht : t = event
    · subst t
      obtain ⟨x, hx⟩ := hmeet
      exact ⟨x, Finset.mem_insert_of_mem (Finset.mem_inter.mp hx).1,
        Finset.mem_insert_of_mem (Finset.mem_inter.mp hx).2⟩
    · exact ⟨b, by simp [switchedRow, ht], by simp [switchedRow, hne]⟩
  intro t s
  obtain ⟨x, hx, hx'⟩ := h t
  obtain ⟨y, hy, hy'⟩ := h s
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨x, hx, hx'⟩)
    (Relation.EqvGen.rel _ _ ⟨y, hy', hy⟩)

omit [DecidableEq R] in
theorem coherent_insert (a : Ω) (J : R → Finset Ω) :
    Incidence.Coherent (fun t => insert a (J t)) := by
  intro t s
  exact Relation.EqvGen.rel _ _ ⟨a, Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩

variable {m : ℕ}

def fourRanks (hm : 4 ≤ m) (base : ZMod m) : Fin 4 ↪ ZMod m where
  toFun i := base + i.val
  inj' i j h := by
    apply Fin.ext
    have he : (i.val : ZMod m) = j.val := add_left_cancel h
    have hv := congrArg ZMod.val he
    simpa only [ZMod.val_natCast_of_lt (i.isLt.trans_le hm),
      ZMod.val_natCast_of_lt (j.isLt.trans_le hm)] using hv

@[simp] theorem fourRanks_zero (hm : 4 ≤ m) (base : ZMod m) : fourRanks hm base 0 = base := by
  simp [fourRanks]

variable [NeZero m]

theorem sum_switchedRows (f : Ω → ZMod m) (a b : Ω) (event : ZMod m)
    (J : ZMod m → Finset Ω) (ha : ∀ t, a ∉ J t) (hb : ∀ t, b ∉ J t) :
    (∑ t : ZMod m, ∑ x ∈ switchedRow a b event t (J t), f x) =
      f a - f b + ∑ t : ZMod m, ∑ x ∈ J t, f x := by
  have hr (t : ZMod m) : (∑ x ∈ switchedRow a b event t (J t), f x) =
      f (if t = event then a else b) + ∑ x ∈ J t, f x := by
    apply Finset.sum_insert
    split_ifs
    · exact ha t
    · exact hb t
  have hi (t : ZMod m) : f (if t = event then a else b) =
      f b + if t = event then f a - f b else 0 := by
    split_ifs <;> simp
  simp only [hr, Finset.sum_add_distrib, hi]
  simp [ZMod.card, nsmul_eq_mul]

end TorusEven.Collar
