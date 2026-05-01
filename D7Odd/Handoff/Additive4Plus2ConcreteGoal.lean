import D7Odd.Handoff.Additive4Plus2BridgeKappa
import D7Odd.Handoff.Additive4Plus2Goal

namespace D7Odd
namespace Handoff
namespace Additive4Plus2

structure BridgeConcreteSkewPackage (m : Nat) [NeZero m] where
  row : Color → ZMod m → Direction
  fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m
  perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3
  baseReturn : Color → D5Odd.ARoot5 m → D5Odd.ARoot5 m
  fiberReturn : Color → D5Odd.ARoot5 m → ARoot3 m → ARoot3 m
  basePoint : Color → D5Odd.ARoot5 m
  period : Color → Nat
  hrow : ∀ t, Function.Bijective fun c : Color => row c t
  hperm : ∀ t base, Function.Bijective (perm t base)
  hReturn : ∀ c bf,
    (bridgeConcreteSchedule row (bridgeD3Phi fiberLayer perm)).returnMap c bf =
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

def BridgeConcreteSkewPackage.toLocalSkewPackage
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcreteSkewPackage m) :
    BridgeLocalSkewPackage m where
  schedule :=
    bridgeConcreteSchedule pkg.row
      (bridgeD3Phi pkg.fiberLayer pkg.perm)
  rawDir := bridgeConcreteRawDir pkg.row
  kappa :=
    bridgeConcreteStateKappa
      (bridgeD3Phi pkg.fiberLayer pkg.perm)
  baseStep := bridgeConcreteBaseStep pkg.row
  fiberStep :=
    bridgeConcreteFiberStep pkg.row pkg.fiberLayer pkg.perm
  baseReturn := pkg.baseReturn
  fiberReturn := pkg.fiberReturn
  basePoint := pkg.basePoint
  period := pkg.period
  hdir := bridgeConcreteRawDir_bijective pkg.row pkg.hrow
  hkappa :=
    bridgeConcreteStateKappa_bijective
      (bridgeD3Phi pkg.fiberLayer pkg.perm)
      (bridgeD3Phi_bijective_of_two_le (by omega)
        pkg.fiberLayer pkg.perm pkg.hperm)
  hschedule := by
    intro t bf c
    rfl
  hbaseLayer := by
    intro t c base fiber
    simp [bridgeConcreteSchedule, bridgeConcreteStateKappa,
      bridgeConcreteBaseStep, bridgeConcreteBaseStepOfRaw,
      bridgeConcreteKappa_baseDirection]
  hfiberLayer := by
    intro t c base fiber
    simp [bridgeConcreteSchedule, bridgeConcreteStateKappa,
      bridgeConcreteFiberStep, bridgeConcreteFiberStepOfRaw,
      bridgeConcreteKappa_fiberDirection]
  hbaseLayerBij := bridgeConcreteBaseStep_bijective hm pkg.row
  hfiberLayerBij :=
    bridgeConcreteFiberStep_bijective_of_two_le (by omega)
      pkg.row pkg.fiberLayer pkg.perm
  hReturn := pkg.hReturn
  hbaseReturnBij := pkg.hbaseReturnBij
  hfiberReturnBij := pkg.hfiberReturnBij
  hreturnBase := pkg.hreturnBase
  hbaseCover := pkg.hbaseCover
  hmonodromy := pkg.hmonodromy

def BridgeConcreteSkewPackage.toCertificate
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcreteSkewPackage m) :
    BridgeProductRootCertificate m :=
  (pkg.toLocalSkewPackage hm).toCertificate

def BridgeOddConcreteSkewTarget : Type :=
  ∀ {m : Nat} [NeZero m], 5 ≤ m → Odd m → BridgeConcreteSkewPackage m

def bridge_odd_local_skew_target_of_concrete_skew_target
    (hConcrete : BridgeOddConcreteSkewTarget) :
    BridgeOddLocalSkewTarget :=
  fun hm hodd => (hConcrete hm hodd).toLocalSkewPackage hm

def bridge_odd_certificate_target_of_concrete_skew_target
    (hConcrete : BridgeOddConcreteSkewTarget) :
    BridgeOddCertificateTarget :=
  fun hm hodd => (hConcrete hm hodd).toCertificate hm

theorem shared_cayley_uniform_from_bridge_odd_concrete_skew_target
    (hConcrete : BridgeOddConcreteSkewTarget) :
    ∀ {m : Nat}, 3 ≤ m → Odd m →
      Shared.CayleyHamiltonDecomposition 7 m :=
  shared_cayley_uniform_from_small3_and_bridge_odd_target
    (bridge_odd_certificate_target_of_concrete_skew_target hConcrete)

end Additive4Plus2
end Handoff
end D7Odd
