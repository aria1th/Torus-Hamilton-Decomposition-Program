-- STATUS: main-path
import TorusEven.Entry.Seed.CorePairs
import TorusEven.Entry.Seed.Small

namespace TorusEven.Entry.Seed

open Collar Incidence

def corePairOrder : Equiv.Perm (Fin 4) where
  toFun := ![0, 3, 1, 2]
  invFun := ![0, 2, 3, 1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def corePairEquiv : Fin 2 × Bool ≃ Fin 4 :=
  ((Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans finProdFinEquiv).trans corePairOrder

abbrev PairIndex (p : ℕ) := Fin 2 ⊕ (Σ h : Fin 3, Fin (Shell.pairCount p h.val))

noncomputable def columnPairs (p : ℕ) (hp : 2 ≤ p) :
    PairIndex p × Bool ≃ Fin 4 ⊕ Shell.Color p :=
  (Equiv.sumProdDistrib _ _ _).trans (Equiv.sumCongr corePairEquiv
    ((Equiv.sigmaProdDistrib (fun h : Fin 3 => Fin (Shell.pairCount p h.val)) Bool).trans
      (Shell.pairEquiv p hp)))

variable (p : ℕ) (hp : 2 ≤ p) {m : ℕ} [NeZero m] (heven : Even m) (hm : 4 ≤ m)
include hm heven

theorem column_pairs_same_xy (hp4 : 4 ≤ p) (j : Fin 3) (hj : j = 0 ∨ j = 1)
    (i : PairIndex p) :
    component p hp heven j (columnPairs p hp (i, false)) =
      component p hp heven j (columnPairs p hp (i, true)) := by
  cases i with
  | inl i =>
    fin_cases i
    · exact core_zero_three_xy p hp heven hm hp4 j hj
    · rcases hj with rfl | rfl
      · exact core_one_two_x p hp heven hm
      · exact core_one_two_y p hp heven hm hp4
  | inr i =>
    obtain ⟨h, i⟩ := i
    have hh : (h.val : ZMod m).val = h.val := ZMod.val_natCast_of_lt (by omega)
    have hc : ∀ k : Fin (Shell.pairCount p (h.val : ZMod m).val),
        component p hp heven j (.inr (Shell.endpoint p hp (h.val : ZMod m).val (k, false))) =
          component p hp heven j (.inr (Shell.endpoint p hp (h.val : ZMod m).val (k, true))) :=
      auxiliary_pair_xy p hp heven hm hp4 j hj (h.val : ZMod m)
    rw [hh] at hc
    exact hc i

theorem evenComponents_ge_four (hp4 : 4 ≤ p) (j : Fin 3) :
    EvenComponents (support p hp heven j) := by
  apply evenComponents_of_pairs _ (columnPairs p hp)
  intro i
  by_cases hj : j = 2
  · subst j
    exact w_connected p hp heven hm _ _
  · apply column_pairs_same_xy p hp heven hm hp4 j _ i
    fin_cases j <;> simp_all

theorem incidence_even_ge_four (hp4 : 4 ≤ p) (j : Fin 3) :
    EvenComponents ((factorization (m := m) p hp).blockSupport xChart j) :=
  (evenComponents_iff p hp heven hm j).mp (evenComponents_ge_four p hp heven hm hp4 j)

theorem evenComponents_all (j : Fin 3) : EvenComponents (support p hp heven j) := by
  by_cases hp4 : 4 ≤ p
  · exact evenComponents_ge_four p hp heven hm hp4 j
  · have hsmall : p = 2 ∨ p = 3 := by omega
    rcases hsmall with rfl | rfl
    · exact smallTwo.evenComponents heven hm j
    · exact smallThree.evenComponents heven hm j

theorem incidence_even (j : Fin 3) :
    EvenComponents ((factorization (m := m) p hp).blockSupport xChart j) :=
  (evenComponents_iff p hp heven hm j).mp (evenComponents_all p hp heven hm j)

end TorusEven.Entry.Seed
