import D5Odd.Cayley
import D7Odd.Cayley
import Shared.D2Seed
import Shared.D3Seed
import RoundComposite

namespace RoundComposite
namespace Concrete

theorem standard_cayley_odd_uniform_2 :
    OddUniformSolved StandardCayleySolved 2 := by
  intro m hm hodd
  exact Shared.D2.shared_cayley_uniform hm hodd

theorem standard_cayley_odd_uniform_3 :
    OddUniformSolved StandardCayleySolved 3 := by
  intro m hm hodd
  exact Shared.D3.shared_cayley_uniform hm hodd

theorem standard_cayley_odd_uniform_5 :
    OddUniformSolved StandardCayleySolved 5 := by
  intro m hm hodd
  exact D5Odd.D5_odd_shared_cayley_uniform hm hodd

theorem standard_cayley_odd_uniform_7 :
    OddUniformSolved StandardCayleySolved 7 := by
  intro m hm hodd
  exact D7Odd.D7_odd_shared_cayley_uniform hm hodd

theorem standard_torus_odd_uniform_5 :
    OddUniformSolved StandardTorusSolved 5 := by
  exact standard_cayley_odd_uniform_5

theorem standard_torus_odd_uniform_2 :
    OddUniformSolved StandardTorusSolved 2 := by
  exact standard_cayley_odd_uniform_2

theorem standard_torus_odd_uniform_3 :
    OddUniformSolved StandardTorusSolved 3 := by
  exact standard_cayley_odd_uniform_3

theorem standard_torus_odd_uniform_7 :
    OddUniformSolved StandardTorusSolved 7 := by
  exact standard_cayley_odd_uniform_7

def OddSuccessorClosureGoal : Prop :=
  ∀ {b m : Nat},
    5 ≤ b →
    Odd m → 3 ≤ m →
    StandardCayleySolved b m →
    StandardCayleySolved (2 * b + 1) m

def OddModulusToriAllDimensionsGoal : Prop :=
  ∀ {d m : Nat}, 2 ≤ d → Odd m → 3 ≤ m →
    Shared.CayleyHamiltonDecomposition d m

theorem standard_cayley_odd_uniform_all_dimensions_of_odd_core
    (hOddCore :
      ∀ {d : Nat}, Odd d → 3 ≤ d →
        OddUniformSolved StandardCayleySolved d) :
    ∀ {d : Nat}, 2 ≤ d →
      OddUniformSolved StandardCayleySolved d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro hd2
      by_cases hdodd : Odd d
      · have hd3 : 3 ≤ d := by
          rcases hdodd with ⟨k, hk⟩
          omega
        exact hOddCore hdodd hd3
      · have hdeven : Even d := Nat.not_odd_iff_even.mp hdodd
        rcases even_iff_exists_two_mul.mp hdeven with ⟨k, hk⟩
        by_cases hk1 : k = 1
        · subst k
          simpa [hk] using standard_cayley_odd_uniform_2
        · have hkpos : 0 < k := by omega
          have hk2 : 2 ≤ k := by omega
          have hklt : k < d := by omega
          rw [hk]
          exact odd_uniform_cayley_mul_of_standard
            (by decide) hkpos
            standard_cayley_odd_uniform_2
            (ih k hklt hk2)

theorem odd_modulus_tori_all_dimensions_uniform_of_odd_core
    (hOddCore :
      ∀ {d : Nat}, 3 ≤ d → Odd d →
        OddUniformSolved StandardCayleySolved d)
    {d : Nat} (hd2 : 2 ≤ d) :
    OddUniformSolved StandardCayleySolved d :=
  standard_cayley_odd_uniform_all_dimensions_of_odd_core
    (fun hodd hd3 => hOddCore hd3 hodd) hd2

theorem odd_modulus_tori_all_dimensions_of_odd_core
    (hOddCore :
      ∀ {d : Nat}, 3 ≤ d → Odd d →
        OddUniformSolved StandardCayleySolved d)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_uniform_of_odd_core
    hOddCore hd2 hm3 hmodd

theorem oddModulusToriAllDimensionsGoal_of_odd_core
    (hOddCore :
      ∀ {d : Nat}, 3 ≤ d → Odd d →
        OddUniformSolved StandardCayleySolved d) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_odd_core
    hOddCore hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_uniform_of_357_and_successor
    (hSucc : OddSuccessorClosureGoal)
    {d : Nat} (hd2 : 2 ≤ d) :
    OddUniformSolved StandardCayleySolved d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro hd2
      by_cases hdodd : Odd d
      · rcases hdodd with ⟨b, rfl⟩
        by_cases h3 : 2 * b + 1 = 3
        · have hb : b = 1 := by omega
          subst b
          simpa using standard_cayley_odd_uniform_3
        by_cases h5 : 2 * b + 1 = 5
        · have hb : b = 2 := by omega
          subst b
          simpa using standard_cayley_odd_uniform_5
        by_cases h7 : 2 * b + 1 = 7
        · have hb : b = 3 := by omega
          subst b
          simpa using standard_cayley_odd_uniform_7
        by_cases h9 : 2 * b + 1 = 9
        · have hb : b = 4 := by omega
          subst b
          simpa using
            (odd_uniform_cayley_mul_of_standard
              (a := 3) (b := 3) (by decide) (by decide)
              standard_cayley_odd_uniform_3 standard_cayley_odd_uniform_3)
        have hb5 : 5 ≤ b := by omega
        have hb2 : 2 ≤ b := by omega
        have hblt : b < 2 * b + 1 := by omega
        intro hm3 hmodd
        exact hSucc hb5 hmodd hm3 ((ih b hblt hb2) hm3 hmodd)
      · have hdeven : Even d := Nat.not_odd_iff_even.mp hdodd
        rcases even_iff_exists_two_mul.mp hdeven with ⟨b, rfl⟩
        by_cases hb1 : b = 1
        · subst b
          simpa using standard_cayley_odd_uniform_2
        have hbpos : 0 < b := by omega
        have hb2 : 2 ≤ b := by omega
        have hblt : b < 2 * b := by omega
        exact odd_uniform_cayley_mul_of_standard
          (a := 2) (b := b) (by decide) hbpos
          standard_cayley_odd_uniform_2 (ih b hblt hb2)

theorem odd_modulus_tori_all_dimensions_of_357_and_successor
    (hSucc : OddSuccessorClosureGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_uniform_of_357_and_successor
    hSucc hd2 hm3 hmodd

theorem oddModulusToriAllDimensionsGoal_of_357_and_successor
    (hSucc : OddSuccessorClosureGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_357_and_successor
    hSucc hd2 hmodd hm3

theorem standard_cayley_odd_uniform_35_of_pointwise
    (hExp : OddPointwiseCompositeExpansion StandardCayleySolved) :
    OddUniformSolved StandardCayleySolved (5 * 7) := by
  exact odd_uniform_mul_of_pointwise StandardCayleySolved hExp
    (by decide) (by decide)
    standard_cayley_odd_uniform_5
    standard_cayley_odd_uniform_7

theorem standard_cayley_odd_uniform_49_of_pointwise
    (hExp : OddPointwiseCompositeExpansion StandardCayleySolved) :
    OddUniformSolved StandardCayleySolved (7 * 7) := by
  exact odd_uniform_mul_of_pointwise StandardCayleySolved hExp
    (by decide) (by decide)
    standard_cayley_odd_uniform_7
    standard_cayley_odd_uniform_7

theorem standard_cayley_odd_uniform_35_of_product :
    OddUniformSolved StandardCayleySolved (5 * 7) := by
  exact odd_uniform_cayley_mul_of_standard
    (by decide) (by decide)
    standard_cayley_odd_uniform_5
    standard_cayley_odd_uniform_7

theorem standard_cayley_odd_uniform_49_of_product :
    OddUniformSolved StandardCayleySolved (7 * 7) := by
  exact odd_uniform_cayley_mul_of_standard
    (by decide) (by decide)
    standard_cayley_odd_uniform_7
    standard_cayley_odd_uniform_7

theorem standard_torus_odd_uniform_35_of_pointwise
    (hExp : OddPointwiseCompositeExpansion StandardTorusSolved) :
    OddUniformSolved StandardTorusSolved (5 * 7) := by
  exact odd_uniform_mul_of_pointwise StandardTorusSolved hExp
    (by decide) (by decide)
    standard_torus_odd_uniform_5
    standard_torus_odd_uniform_7

theorem standard_torus_odd_uniform_49_of_pointwise
    (hExp : OddPointwiseCompositeExpansion StandardTorusSolved) :
    OddUniformSolved StandardTorusSolved (7 * 7) := by
  exact odd_uniform_mul_of_pointwise StandardTorusSolved hExp
    (by decide) (by decide)
    standard_torus_odd_uniform_7
    standard_torus_odd_uniform_7

theorem standard_torus_odd_uniform_35_of_product :
    OddUniformSolved StandardTorusSolved (5 * 7) := by
  exact standard_torus_odd_uniform_35_of_pointwise
    standard_torus_odd_pointwise_composite_expansion

theorem standard_torus_odd_uniform_49_of_product :
    OddUniformSolved StandardTorusSolved (7 * 7) := by
  exact standard_torus_odd_uniform_49_of_pointwise
    standard_torus_odd_pointwise_composite_expansion

theorem standard_cayley_odd_uniform_35_of_left_coordinatized_5
    (hCoord5 : OddUniformSolved StandardCoordinatizedCayleySolved 5) :
    OddUniformSolved StandardCayleySolved (5 * 7) := by
  exact odd_uniform_cayley_mul_of_left_coordinatized
    (by decide) (by decide)
    hCoord5
    standard_cayley_odd_uniform_7

theorem standard_cayley_odd_uniform_49_of_left_coordinatized_7
    (hCoord7 : OddUniformSolved StandardCoordinatizedCayleySolved 7) :
    OddUniformSolved StandardCayleySolved (7 * 7) := by
  exact odd_uniform_cayley_mul_of_left_coordinatized
    (by decide) (by decide)
    hCoord7
    standard_cayley_odd_uniform_7

theorem standard_cayley_odd_uniform_product_of_5_7_list
    (hExp : OddPointwiseCompositeExpansion StandardCayleySolved)
    {ds : List Nat} (hne : ds ≠ [])
    (hmem : ∀ d, d ∈ ds → d = 5 ∨ d = 7) :
    OddUniformSolved StandardCayleySolved ds.prod := by
  cases ds with
  | nil =>
      exact (hne rfl).elim
  | cons d ds =>
      exact odd_uniform_prod_cons_of_pointwise StandardCayleySolved hExp
        (fun e he => by
          rcases hmem e he with rfl | rfl <;> decide)
        (fun e he => by
          rcases hmem e he with rfl | rfl
          · exact standard_cayley_odd_uniform_5
          · exact standard_cayley_odd_uniform_7)

theorem standard_cayley_odd_uniform_product_of_5_7_list_of_product
    {ds : List Nat} (hne : ds ≠ [])
    (hmem : ∀ d, d ∈ ds → d = 5 ∨ d = 7) :
    OddUniformSolved StandardCayleySolved ds.prod := by
  cases ds with
  | nil =>
      exact (hne rfl).elim
  | cons d ds =>
      exact odd_uniform_standard_cayley_prod_cons_of_product
        (fun e he => by
          rcases hmem e he with rfl | rfl <;> decide)
        (fun e he => by
          rcases hmem e he with rfl | rfl
          · exact standard_cayley_odd_uniform_5
          · exact standard_cayley_odd_uniform_7)

theorem standard_torus_odd_uniform_product_of_5_7_list_of_product
    {ds : List Nat} (hne : ds ≠ [])
    (hmem : ∀ d, d ∈ ds → d = 5 ∨ d = 7) :
    OddUniformSolved StandardTorusSolved ds.prod := by
  cases ds with
  | nil =>
      exact (hne rfl).elim
  | cons d ds =>
      exact odd_uniform_prod_cons_of_pointwise StandardTorusSolved
        standard_torus_odd_pointwise_composite_expansion
        (fun e he => by
          rcases hmem e he with rfl | rfl <;> decide)
        (fun e he => by
          rcases hmem e he with rfl | rfl
          · exact standard_torus_odd_uniform_5
          · exact standard_torus_odd_uniform_7)

end Concrete
end RoundComposite
