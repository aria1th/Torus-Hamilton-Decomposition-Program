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

end Concrete
end RoundComposite
