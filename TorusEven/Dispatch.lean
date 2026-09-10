-- STATUS: main-path
import Shared.CayleyProduct
import Shared.D2Seed

/-!
# Parity-neutral dimension dispatcher

The odd-modulus dispatcher
`RoundComposite.Concrete.odd_modulus_tori_all_dimensions_uniform_of_357_and_successor`
recurses on the dimension `d` and only threads the modulus parity through to the seeds.
This file restates that recursion for an arbitrary class of moduli closed under positive
powers, using only the parity-free product theorem
`Shared.cayleyHamiltonDecomposition_product_of_left_coordinatized`.

Nothing here depends on the odd high-modulus core.
-/

namespace TorusEven

/-- The solved predicate shared with the odd endpoint. -/
abbrev Solved (d m : Nat) : Prop := Shared.CayleyHamiltonDecomposition d m

/-- A class of moduli that is closed under positive powers and bounded below by `3`. -/
structure ModulusClass where
  P : Nat → Prop
  three_le : ∀ {m : Nat}, P m → 3 ≤ m
  pow_closed : ∀ {m a : Nat}, 0 < a → P m → P (m ^ a)

/-- `Solved d m` for every modulus in the class. -/
def ModulusClass.Uniform (C : ModulusClass) (d : Nat) : Prop :=
  ∀ {m : Nat}, C.P m → Solved d m

theorem three_le_pow_of_three_le {m a : Nat} (hm : 3 ≤ m) (ha : 0 < a) :
    3 ≤ m ^ a :=
  le_trans hm (Nat.le_self_pow (Nat.ne_of_gt ha) m)

/-- Dimension product: `D_a(m)` and `D_b(m^a)` give `D_{ab}(m)`.  Parity-free. -/
theorem solved_mul {a b m : Nat} (ha : 0 < a) (_hb : 0 < b) (hm : 3 ≤ m)
    (hA : Solved a m) (hB : Solved b (m ^ a)) : Solved (a * b) m := by
  have hpow3 : 3 ≤ m ^ a := three_le_pow_of_three_le hm ha
  have hpow1 : 1 < m ^ a := by omega
  letI : NeZero m := ⟨by omega⟩
  letI : NeZero (m ^ a) := ⟨by omega⟩
  exact Shared.cayleyHamiltonDecomposition_product_of_left_coordinatized
    (Shared.coordinatizedCayleyHamiltonDecomposition_of_single_cycle hpow1 hA) hB

theorem ModulusClass.uniform_mul (C : ModulusClass) {a b : Nat}
    (ha : 0 < a) (hb : 0 < b)
    (hA : C.Uniform a) (hB : C.Uniform b) : C.Uniform (a * b) := by
  refine fun {m} hm => ?_
  exact solved_mul ha hb (C.three_le hm) (hA hm) (hB (C.pow_closed ha hm))

/-- `D_2(m)` for every modulus at least `3`, from `Shared.D2`. -/
theorem ModulusClass.uniform_two (C : ModulusClass) : C.Uniform 2 := by
  refine fun {m} hm => ?_
  have h3 : 3 ≤ m := C.three_le hm
  haveI : NeZero m := ⟨by omega⟩
  exact Shared.D2.cayleyHamiltonDecomposition

/-- Successor closure in the shape used by the odd dispatcher. -/
def ModulusClass.SuccessorClosure (C : ModulusClass) : Prop :=
  ∀ {b m : Nat}, 5 ≤ b → C.P m → Solved b m → Solved (2 * b + 1) m

/-- Odd degrees at least seven, as supplied by the manuscript's collar route. -/
def ModulusClass.OddDegreeClosure (C : ModulusClass) : Prop :=
  ∀ {d m : Nat}, Odd d → 7 ≤ d → C.P m → Solved d m

/-- Powers of two, from the `d = 2` seed alone. -/
theorem ModulusClass.uniform_two_pow (C : ModulusClass) :
    ∀ k : Nat, 1 ≤ k → C.Uniform (2 ^ k) := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
      intro _
      by_cases hk : k = 0
      · subst hk
        simp only [zero_add, pow_one]
        exact C.uniform_two
      · have hk1 : 1 ≤ k := by omega
        have h : C.Uniform (2 * 2 ^ k) := C.uniform_mul (a := 2) (b := 2 ^ k) (by decide)
          (Nat.two_pow_pos k) C.uniform_two (ih hk1)
        rw [pow_succ, Nat.mul_comm]
        exact h

/-- The odd-dispatcher recursion, parity-neutral: seeds `2,3,5,7` and a successor closure. -/
theorem ModulusClass.uniform_of_seeds_and_successor (C : ModulusClass)
    (h3 : C.Uniform 3) (h5 : C.Uniform 5) (h7 : C.Uniform 7)
    (hSucc : C.SuccessorClosure) :
    ∀ {d : Nat}, 2 ≤ d → C.Uniform d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro hd2
      refine fun {m} hm => ?_
      by_cases hdodd : Odd d
      · rcases hdodd with ⟨b, rfl⟩
        by_cases hb1 : b = 1
        · subst hb1; simpa using h3 hm
        by_cases hb2 : b = 2
        · subst hb2; simpa using h5 hm
        by_cases hb3 : b = 3
        · subst hb3; simpa using h7 hm
        by_cases hb4 : b = 4
        · subst hb4
          simpa using C.uniform_mul (a := 3) (b := 3) (by decide) (by decide) h3 h3 hm
        have hb5 : 5 ≤ b := by omega
        have hbge2 : 2 ≤ b := by omega
        have hblt : b < 2 * b + 1 := by omega
        exact hSucc hb5 hm (ih b hblt hbge2 hm)
      · have hdeven : Even d := Nat.not_odd_iff_even.mp hdodd
        rcases even_iff_exists_two_mul.mp hdeven with ⟨b, rfl⟩
        by_cases hb1 : b = 1
        · subst hb1; simpa using C.uniform_two hm
        have hbpos : 0 < b := by omega
        have hbge2 : 2 ≤ b := by omega
        have hblt : b < 2 * b := by omega
        exact C.uniform_mul (a := 2) (b := b) (by decide) hbpos C.uniform_two
          (ih b hblt hbge2) hm

/-- The manuscript's case split: even `d` by products, `d = 3, 5` seeds, odd `d ≥ 7` direct. -/
theorem ModulusClass.uniform_of_seeds_and_odd_degree (C : ModulusClass)
    (h3 : C.Uniform 3) (h5 : C.Uniform 5) (hOdd : C.OddDegreeClosure) :
    ∀ {d : Nat}, 2 ≤ d → C.Uniform d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro hd2
      refine fun {m} hm => ?_
      by_cases hdodd : Odd d
      · by_cases hd3 : d = 3
        · subst hd3; exact h3 hm
        by_cases hd5 : d = 5
        · subst hd5; exact h5 hm
        have hd7 : 7 ≤ d := by
          rcases hdodd with ⟨b, hb⟩; omega
        exact hOdd hdodd hd7 hm
      · have hdeven : Even d := Nat.not_odd_iff_even.mp hdodd
        rcases even_iff_exists_two_mul.mp hdeven with ⟨b, rfl⟩
        by_cases hb1 : b = 1
        · subst hb1; simpa using C.uniform_two hm
        have hbpos : 0 < b := by omega
        have hbge2 : 2 ≤ b := by omega
        have hblt : b < 2 * b := by omega
        exact C.uniform_mul (a := 2) (b := b) (by decide) hbpos C.uniform_two
          (ih b hblt hbge2) hm

/-- Even moduli at least four. -/
def evenClass : ModulusClass where
  P m := Even m ∧ 4 ≤ m
  three_le h := by omega
  pow_closed ha h :=
    ⟨h.1.pow_of_ne_zero (Nat.ne_of_gt ha),
      le_trans h.2 (Nat.le_self_pow (Nat.ne_of_gt ha) _)⟩

/-- Odd moduli at least three (the class of the existing endpoint). -/
def oddClass : ModulusClass where
  P m := Odd m ∧ 3 ≤ m
  three_le h := h.2
  pow_closed ha h := ⟨h.1.pow, three_le_pow_of_three_le h.2 ha⟩

/-- Unconditional: `D_{2^k}(m)` for every even `m ≥ 4` and `k ≥ 1`. -/
theorem even_two_pow_dimensions {k m : Nat} (hk : 1 ≤ k) (hm : Even m) (hm4 : 4 ≤ m) :
    Solved (2 ^ k) m :=
  evenClass.uniform_two_pow k hk ⟨hm, hm4⟩

end TorusEven
