import D5Odd.Cayley
import D7Odd.Cayley
import RoundComposite

namespace RoundComposite
namespace Concrete

theorem standard_cayley_odd_uniform_5 :
    OddUniformSolved StandardCayleySolved 5 := by
  intro m hm hodd
  exact D5Odd.D5_odd_shared_cayley_uniform hm hodd

theorem standard_cayley_odd_uniform_7 :
    OddUniformSolved StandardCayleySolved 7 := by
  intro m hm hodd
  exact D7Odd.D7_odd_shared_cayley_uniform hm hodd

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

end Concrete
end RoundComposite
