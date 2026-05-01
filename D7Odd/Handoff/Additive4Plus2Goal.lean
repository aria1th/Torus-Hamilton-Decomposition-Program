import D7Odd.Handoff.SmallBranches
import D7Odd.Handoff.Additive4Plus2Endpoints

namespace D7Odd
namespace Handoff
namespace Additive4Plus2

def BridgeOddCertificateTarget : Type :=
  ∀ {m : Nat} [NeZero m], 5 ≤ m → Odd m → BridgeProductRootCertificate m

theorem five_le_of_three_le_odd_ne_three {m : Nat}
    (hm3 : 3 ≤ m) (hodd : Odd m) (hne3 : m ≠ 3) :
    5 ≤ m := by
  have hne4 : m ≠ 4 := by
    intro h4
    subst m
    rcases hodd with ⟨k, hk⟩
    omega
  omega

theorem handoff_from_small3_and_bridge_odd_target
    (hBridge : BridgeOddCertificateTarget)
    {m : Nat} [NeZero m] (hm3 : 3 ≤ m) (hodd : Odd m) :
    HamiltonDecompositionD7 m := by
  by_cases h3 : m = 3
  · subst m
    exact smallHamilton3
  · exact (hBridge
      (five_le_of_three_le_odd_ne_three hm3 hodd h3) hodd).toHamiltonDecompositionD7

theorem torus_from_small3_and_bridge_odd_target
    (hBridge : BridgeOddCertificateTarget)
    {m : Nat} [NeZero m] (hm3 : 3 ≤ m) (hodd : Odd m) :
    D7Odd.TorusHamiltonDecompositionD7 m :=
  D7Odd.torusHamiltonDecompositionD7_of_handoff
    (handoff_from_small3_and_bridge_odd_target hBridge hm3 hodd)

theorem cayley_from_small3_and_bridge_odd_target
    (hBridge : BridgeOddCertificateTarget)
    {m : Nat} [NeZero m] (hm3 : 3 ≤ m) (hodd : Odd m) :
    D7Odd.CayleyHamiltonDecompositionD7 m :=
  D7Odd.cayleyHamiltonDecomposition_of_torus
    (torus_from_small3_and_bridge_odd_target hBridge hm3 hodd)

theorem shared_cayley_from_small3_and_bridge_odd_target
    (hBridge : BridgeOddCertificateTarget)
    {m : Nat} [NeZero m] (hm3 : 3 ≤ m) (hodd : Odd m) :
    Shared.CayleyHamiltonDecomposition 7 m :=
  D7Odd.sharedCayleyHamiltonDecomposition_of_cayley
    (cayley_from_small3_and_bridge_odd_target hBridge hm3 hodd)

theorem shared_cayley_uniform_from_small3_and_bridge_odd_target
    (hBridge : BridgeOddCertificateTarget) :
    ∀ {m : Nat}, 3 ≤ m → Odd m →
      Shared.CayleyHamiltonDecomposition 7 m := by
  intro m hm3 hodd
  haveI : NeZero m := ⟨by omega⟩
  exact shared_cayley_from_small3_and_bridge_odd_target hBridge hm3 hodd

end Additive4Plus2
end Handoff
end D7Odd
