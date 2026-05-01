import D7Odd.Handoff.Main

namespace D7Odd

def D7OddConditionalTarget : Prop :=
  Handoff.MainOddTheoremTarget

theorem D7_odd_from_handoff_branches
    (small : Handoff.SmallBranchResults)
    (generic : Handoff.GenericOddBranchResult)
    {m : Nat} [NeZero m] (hm3 : 3 <= m) (hodd : Odd m) :
    Handoff.HamiltonDecompositionD7 m :=
  Handoff.odd_from_branches small generic hm3 hodd

end D7Odd
