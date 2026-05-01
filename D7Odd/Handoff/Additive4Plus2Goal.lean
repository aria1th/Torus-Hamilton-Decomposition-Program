import D7Odd.Handoff.SmallBranches
import D7Odd.Handoff.Additive4Plus2Endpoints

namespace D7Odd
namespace Handoff
namespace Additive4Plus2

def BridgeOddCertificateTarget : Type :=
  ∀ {m : Nat} [NeZero m], 5 ≤ m → Odd m → BridgeProductRootCertificate m

structure BridgeLocalSkewPackage (m : Nat) [NeZero m] where
  schedule : BridgeProductRootSchedule m
  rawDir : ZMod m → ProductRoot m → Color → Direction
  kappa : ZMod m → ProductRoot m → Direction → Direction
  baseStep :
    ZMod m → Color → D5Odd.ARoot5 m → D5Odd.ARoot5 m
  fiberStep :
    ZMod m → Color → D5Odd.ARoot5 m → ARoot3 m → ARoot3 m
  baseReturn : Color → D5Odd.ARoot5 m → D5Odd.ARoot5 m
  fiberReturn : Color → D5Odd.ARoot5 m → ARoot3 m → ARoot3 m
  basePoint : Color → D5Odd.ARoot5 m
  period : Color → Nat
  hdir : ∀ t bf, Function.Bijective (rawDir t bf)
  hkappa : ∀ t bf, Function.Bijective (kappa t bf)
  hschedule : ∀ t bf c, schedule.dir t bf c = kappa t bf (rawDir t bf c)
  hbaseLayer : ∀ t c base fiber,
    baseAddQ (baseDirectionOfSlot (schedule.dir t (base, fiber) c)) base =
      baseStep t c base
  hfiberLayer : ∀ t c base fiber,
    fiberAddQ (bridgeFiberDirectionOfSlot (schedule.dir t (base, fiber) c))
        fiber =
      fiberStep t c base fiber
  hbaseLayerBij : ∀ t c, Function.Bijective (baseStep t c)
  hfiberLayerBij : ∀ t c base, Function.Bijective (fiberStep t c base)
  hReturn : ∀ c bf,
    schedule.returnMap c bf =
      Shared.skewProductMap (baseReturn c) (fiberReturn c) bf
  hbaseReturnBij : ∀ c, Function.Bijective (baseReturn c)
  hfiberReturnBij : ∀ c u, Function.Bijective (fiberReturn c u)
  hreturnBase : ∀ c, ((baseReturn c)^[period c]) (basePoint c) = basePoint c
  hbaseCover : ∀ c b, ∃ k : Nat,
    k < period c ∧ ((baseReturn c)^[k]) (basePoint c) = b
  hmonodromy : ∀ c,
    IsSingleCycleMap
      (Shared.sectionReturn
        (Shared.skewProductMap (baseReturn c) (fiberReturn c))
        (basePoint c) (period c))

def BridgeLocalSkewPackage.toCertificate
    {m : Nat} [NeZero m] (pkg : BridgeLocalSkewPackage m) :
    BridgeProductRootCertificate m :=
  BridgeProductRootCertificate.ofLocalBridgeAndSkewReturns
    pkg.schedule pkg.rawDir pkg.kappa pkg.baseStep pkg.fiberStep
    pkg.baseReturn pkg.fiberReturn pkg.basePoint pkg.period
    pkg.hdir pkg.hkappa pkg.hschedule pkg.hbaseLayer pkg.hfiberLayer
    pkg.hbaseLayerBij pkg.hfiberLayerBij pkg.hReturn pkg.hbaseReturnBij
    pkg.hfiberReturnBij pkg.hreturnBase pkg.hbaseCover pkg.hmonodromy

def BridgeOddLocalSkewTarget : Type :=
  ∀ {m : Nat} [NeZero m], 5 ≤ m → Odd m → BridgeLocalSkewPackage m

def bridge_odd_certificate_target_of_local_skew_target
    (hLocal : BridgeOddLocalSkewTarget) :
    BridgeOddCertificateTarget :=
  fun hm5 hodd => (hLocal hm5 hodd).toCertificate

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

theorem shared_cayley_uniform_from_bridge_odd_local_skew_target
    (hLocal : BridgeOddLocalSkewTarget) :
    ∀ {m : Nat}, 3 ≤ m → Odd m →
      Shared.CayleyHamiltonDecomposition 7 m :=
  shared_cayley_uniform_from_small3_and_bridge_odd_target
    (bridge_odd_certificate_target_of_local_skew_target hLocal)

end Additive4Plus2
end Handoff
end D7Odd
