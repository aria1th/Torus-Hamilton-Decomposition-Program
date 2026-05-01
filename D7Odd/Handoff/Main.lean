import D7Odd.Handoff.CanonicalCountMatrices
import D7Odd.Handoff.SmallCertificates

namespace D7Odd
namespace Handoff

structure SmallBranchResults where
  m3 : HamiltonDecompositionD7 3
  m5 : HamiltonDecompositionD7 5

structure GenericOddBranchResult where
  ge7 : ∀ {m : Nat} [NeZero m], 7 ≤ m → Odd m → HamiltonDecompositionD7 m

theorem odd_from_branches
    (small : SmallBranchResults)
    (generic : GenericOddBranchResult)
    {m : Nat} [NeZero m] (hm3 : 3 ≤ m) (hodd : Odd m) :
    HamiltonDecompositionD7 m := by
  by_cases h3 : m = 3
  · subst m
    exact small.m3
  · by_cases h5 : m = 5
    · subst m
      exact small.m5
    · by_cases hm7 : 7 ≤ m
      · exact generic.ge7 hm7 hodd
      · have hmle6 : m ≤ 6 := by omega
        interval_cases m
        · contradiction
        · norm_num at hodd
        · contradiction
        · norm_num at hodd

def MainOddTheoremTarget : Prop :=
  ∀ {m : Nat} [NeZero m], 3 ≤ m → Odd m → HamiltonDecompositionD7 m

end Handoff
end D7Odd
