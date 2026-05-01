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

def bridgeConcreteReturnFold {m : Nat}
    (row : Color → ZMod m → Direction)
    (fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m)
    (perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3)
    (c : Color) : ProductRoot m → ProductRoot m :=
  fun bf => (List.range m).foldl
    (fun x (t : Nat) =>
      Shared.skewProductMap
        (bridgeConcreteBaseStep row (t : ZMod m) c)
        (bridgeConcreteFiberStep row fiberLayer perm (t : ZMod m) c) x)
    bf

def bridgeConcreteBaseReturn {m : Nat}
    (row : Color → ZMod m → Direction)
    (c : Color) : D5Odd.ARoot5 m → D5Odd.ARoot5 m :=
  fun base => (List.range m).foldl
    (fun x (t : Nat) => bridgeConcreteBaseStep row (t : ZMod m) c x)
    base

def bridgeConcreteFiberReturn {m : Nat}
    (row : Color → ZMod m → Direction)
    (fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m)
    (perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3)
    (c : Color) :
    D5Odd.ARoot5 m → ARoot3 m → ARoot3 m :=
  fun base fiber =>
    (bridgeConcreteReturnFold row fiberLayer perm c (base, fiber)).2

theorem bridgeConcreteReturnFold_fst {m : Nat}
    (row : Color → ZMod m → Direction)
    (fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m)
    (perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3)
    (c : Color) (bf : ProductRoot m) :
    (bridgeConcreteReturnFold row fiberLayer perm c bf).1 =
      bridgeConcreteBaseReturn row c bf.1 := by
  rcases bf with ⟨base, fiber⟩
  unfold bridgeConcreteReturnFold bridgeConcreteBaseReturn
  let ts := List.range m
  change
    (ts.foldl
        (fun x (t : Nat) =>
          Shared.skewProductMap
            (bridgeConcreteBaseStep row (t : ZMod m) c)
            (bridgeConcreteFiberStep row fiberLayer perm
              (t : ZMod m) c) x)
        (base, fiber)).1 =
      ts.foldl
        (fun x (t : Nat) => bridgeConcreteBaseStep row (t : ZMod m) c x)
        base
  clear_value ts
  induction ts generalizing base fiber with
  | nil =>
      simp
  | cons t ts ih =>
      simpa [Shared.skewProductMap] using
        ih (bridgeConcreteBaseStep row (t : ZMod m) c base)
          (bridgeConcreteFiberStep row fiberLayer perm
            (t : ZMod m) c base fiber)

theorem bridgeConcreteReturnFold_eq_skewProductMap {m : Nat}
    (row : Color → ZMod m → Direction)
    (fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m)
    (perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3)
    (c : Color) :
    bridgeConcreteReturnFold row fiberLayer perm c =
      Shared.skewProductMap
        (bridgeConcreteBaseReturn row c)
        (bridgeConcreteFiberReturn row fiberLayer perm c) := by
  funext bf
  exact Prod.ext
    (bridgeConcreteReturnFold_fst row fiberLayer perm c bf)
    rfl

theorem bridgeConcreteSchedule_returnMap_eq_returnFold
    {m : Nat} [NeZero m]
    (row : Color → ZMod m → Direction)
    (fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m)
    (perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3)
    (c : Color) (bf : ProductRoot m) :
    (bridgeConcreteSchedule row (bridgeD3Phi fiberLayer perm)).returnMap c bf =
      bridgeConcreteReturnFold row fiberLayer perm c bf := by
  unfold BridgeProductRootSchedule.returnMap bridgeConcreteReturnFold
  let ts := List.range m
  change
    ts.foldl
        (fun x (t : Nat) =>
          (bridgeConcreteSchedule row (bridgeD3Phi fiberLayer perm)).layerMap
            (t : ZMod m) c x)
        bf =
      ts.foldl
        (fun x (t : Nat) =>
          Shared.skewProductMap
            (bridgeConcreteBaseStep row (t : ZMod m) c)
            (bridgeConcreteFiberStep row fiberLayer perm
              (t : ZMod m) c) x)
        bf
  clear_value ts
  induction ts generalizing bf with
  | nil =>
      simp
  | cons t ts ih =>
      rw [List.foldl_cons, List.foldl_cons]
      rw [bridgeConcreteSchedule_layerMap_eq_skewProductMap
        row fiberLayer perm (t : ZMod m) c]
      exact ih _

theorem bridgeConcreteSchedule_returnMap_eq_skewProductMap
    {m : Nat} [NeZero m]
    (row : Color → ZMod m → Direction)
    (fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m)
    (perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3)
    (c : Color) (bf : ProductRoot m) :
    (bridgeConcreteSchedule row (bridgeD3Phi fiberLayer perm)).returnMap c bf =
      Shared.skewProductMap
        (bridgeConcreteBaseReturn row c)
        (bridgeConcreteFiberReturn row fiberLayer perm c) bf := by
  rw [bridgeConcreteSchedule_returnMap_eq_returnFold row fiberLayer perm c bf]
  exact congrFun
    (bridgeConcreteReturnFold_eq_skewProductMap row fiberLayer perm c) bf

theorem bridgeConcreteBaseReturn_bijective
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (row : Color → ZMod m → Direction) (c : Color) :
    Function.Bijective (bridgeConcreteBaseReturn row c) := by
  unfold bridgeConcreteBaseReturn
  exact foldl_bijective_of_forall_mem (List.range m)
    (fun t base => bridgeConcreteBaseStep row (t : ZMod m) c base)
    (by
      intro t _ht
      exact bridgeConcreteBaseStep_bijective hm row (t : ZMod m) c)

theorem bridgeConcreteFiberReturn_bijective
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (row : Color → ZMod m → Direction)
    (fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m)
    (perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3)
    (c : Color) (base : D5Odd.ARoot5 m) :
    Function.Bijective (bridgeConcreteFiberReturn row fiberLayer perm c base) := by
  unfold bridgeConcreteFiberReturn bridgeConcreteReturnFold
  let ts := List.range m
  change Function.Bijective
    (fun fiber =>
      (ts.foldl
        (fun x (t : Nat) =>
          Shared.skewProductMap
            (bridgeConcreteBaseStep row (t : ZMod m) c)
            (bridgeConcreteFiberStep row fiberLayer perm
              (t : ZMod m) c) x)
        (base, fiber)).2)
  clear_value ts
  induction ts generalizing base with
  | nil =>
      simp
  | cons t ts ih =>
      change Function.Bijective
        ((fun fiber =>
          (ts.foldl
            (fun x (t : Nat) =>
              Shared.skewProductMap
                (bridgeConcreteBaseStep row (t : ZMod m) c)
                (bridgeConcreteFiberStep row fiberLayer perm
                  (t : ZMod m) c) x)
            (bridgeConcreteBaseStep row (t : ZMod m) c base, fiber)).2) ∘
          bridgeConcreteFiberStep row fiberLayer perm
            (t : ZMod m) c base)
      exact Function.Bijective.comp
        (ih (bridgeConcreteBaseStep row (t : ZMod m) c base))
        (bridgeConcreteFiberStep_bijective_of_two_le (by omega)
          row fiberLayer perm (t : ZMod m) c base)

structure BridgeConcreteReturnPackage (m : Nat) [NeZero m] where
  row : Color → ZMod m → Direction
  fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m
  perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3
  basePoint : Color → D5Odd.ARoot5 m
  period : Color → Nat
  hrow : ∀ t, Function.Bijective fun c : Color => row c t
  hperm : ∀ t base, Function.Bijective (perm t base)
  hbaseReturnBij : ∀ c,
    Function.Bijective (bridgeConcreteBaseReturn row c)
  hfiberReturnBij : ∀ c u,
    Function.Bijective (bridgeConcreteFiberReturn row fiberLayer perm c u)
  hreturnBase : ∀ c,
    ((bridgeConcreteBaseReturn row c)^[period c]) (basePoint c) =
      basePoint c
  hbaseCover : ∀ c b, ∃ k : Nat,
    k < period c ∧
      ((bridgeConcreteBaseReturn row c)^[k]) (basePoint c) = b
  hmonodromy : ∀ c,
    IsSingleCycleMap
      (Shared.sectionReturn
        (Shared.skewProductMap
          (bridgeConcreteBaseReturn row c)
          (bridgeConcreteFiberReturn row fiberLayer perm c))
        (basePoint c) (period c))

def BridgeConcreteReturnPackage.toConcreteSkewPackage
    {m : Nat} [NeZero m] (pkg : BridgeConcreteReturnPackage m) :
    BridgeConcreteSkewPackage m where
  row := pkg.row
  fiberLayer := pkg.fiberLayer
  perm := pkg.perm
  baseReturn := bridgeConcreteBaseReturn pkg.row
  fiberReturn := bridgeConcreteFiberReturn pkg.row pkg.fiberLayer pkg.perm
  basePoint := pkg.basePoint
  period := pkg.period
  hrow := pkg.hrow
  hperm := pkg.hperm
  hReturn :=
    bridgeConcreteSchedule_returnMap_eq_skewProductMap
      pkg.row pkg.fiberLayer pkg.perm
  hbaseReturnBij := pkg.hbaseReturnBij
  hfiberReturnBij := pkg.hfiberReturnBij
  hreturnBase := pkg.hreturnBase
  hbaseCover := pkg.hbaseCover
  hmonodromy := pkg.hmonodromy

def BridgeConcreteReturnPackage.toLocalSkewPackage
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcreteReturnPackage m) :
    BridgeLocalSkewPackage m :=
  pkg.toConcreteSkewPackage.toLocalSkewPackage hm

def BridgeConcreteReturnPackage.toCertificate
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcreteReturnPackage m) :
    BridgeProductRootCertificate m :=
  pkg.toConcreteSkewPackage.toCertificate hm

structure BridgeConcreteOrbitPackage (m : Nat) [NeZero m] where
  row : Color → ZMod m → Direction
  fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m
  perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3
  basePoint : Color → D5Odd.ARoot5 m
  period : Color → Nat
  hrow : ∀ t, Function.Bijective fun c : Color => row c t
  hperm : ∀ t base, Function.Bijective (perm t base)
  hreturnBase : ∀ c,
    ((bridgeConcreteBaseReturn row c)^[period c]) (basePoint c) =
      basePoint c
  hbaseCover : ∀ c b, ∃ k : Nat,
    k < period c ∧
      ((bridgeConcreteBaseReturn row c)^[k]) (basePoint c) = b
  hmonodromy : ∀ c,
    IsSingleCycleMap
      (Shared.sectionReturn
        (Shared.skewProductMap
          (bridgeConcreteBaseReturn row c)
          (bridgeConcreteFiberReturn row fiberLayer perm c))
        (basePoint c) (period c))

def BridgeConcreteOrbitPackage.toConcreteReturnPackage
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcreteOrbitPackage m) :
    BridgeConcreteReturnPackage m where
  row := pkg.row
  fiberLayer := pkg.fiberLayer
  perm := pkg.perm
  basePoint := pkg.basePoint
  period := pkg.period
  hrow := pkg.hrow
  hperm := pkg.hperm
  hbaseReturnBij := bridgeConcreteBaseReturn_bijective hm pkg.row
  hfiberReturnBij :=
    bridgeConcreteFiberReturn_bijective hm pkg.row pkg.fiberLayer pkg.perm
  hreturnBase := pkg.hreturnBase
  hbaseCover := pkg.hbaseCover
  hmonodromy := pkg.hmonodromy

def BridgeConcreteOrbitPackage.toConcreteSkewPackage
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcreteOrbitPackage m) :
    BridgeConcreteSkewPackage m :=
  (pkg.toConcreteReturnPackage hm).toConcreteSkewPackage

def BridgeConcreteOrbitPackage.toLocalSkewPackage
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcreteOrbitPackage m) :
    BridgeLocalSkewPackage m :=
  (pkg.toConcreteReturnPackage hm).toLocalSkewPackage hm

def BridgeConcreteOrbitPackage.toCertificate
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcreteOrbitPackage m) :
    BridgeProductRootCertificate m :=
  (pkg.toConcreteReturnPackage hm).toCertificate hm

def BridgeOddConcreteSkewTarget : Type :=
  ∀ {m : Nat} [NeZero m], 5 ≤ m → Odd m → BridgeConcreteSkewPackage m

def BridgeOddConcreteReturnTarget : Type :=
  ∀ {m : Nat} [NeZero m], 5 ≤ m → Odd m → BridgeConcreteReturnPackage m

def BridgeOddConcreteOrbitTarget : Type :=
  ∀ {m : Nat} [NeZero m], 5 ≤ m → Odd m → BridgeConcreteOrbitPackage m

def bridge_odd_local_skew_target_of_concrete_skew_target
    (hConcrete : BridgeOddConcreteSkewTarget) :
    BridgeOddLocalSkewTarget :=
  fun hm hodd => (hConcrete hm hodd).toLocalSkewPackage hm

def bridge_odd_certificate_target_of_concrete_skew_target
    (hConcrete : BridgeOddConcreteSkewTarget) :
    BridgeOddCertificateTarget :=
  fun hm hodd => (hConcrete hm hodd).toCertificate hm

def bridge_odd_concrete_skew_target_of_concrete_return_target
    (hReturn : BridgeOddConcreteReturnTarget) :
    BridgeOddConcreteSkewTarget :=
  fun hm hodd => (hReturn hm hodd).toConcreteSkewPackage

def bridge_odd_certificate_target_of_concrete_return_target
    (hReturn : BridgeOddConcreteReturnTarget) :
    BridgeOddCertificateTarget :=
  bridge_odd_certificate_target_of_concrete_skew_target
    (bridge_odd_concrete_skew_target_of_concrete_return_target hReturn)

def bridge_odd_concrete_return_target_of_concrete_orbit_target
    (hOrbit : BridgeOddConcreteOrbitTarget) :
    BridgeOddConcreteReturnTarget :=
  fun hm hodd => (hOrbit hm hodd).toConcreteReturnPackage hm

def bridge_odd_certificate_target_of_concrete_orbit_target
    (hOrbit : BridgeOddConcreteOrbitTarget) :
    BridgeOddCertificateTarget :=
  bridge_odd_certificate_target_of_concrete_return_target
    (bridge_odd_concrete_return_target_of_concrete_orbit_target hOrbit)

theorem shared_cayley_uniform_from_bridge_odd_concrete_skew_target
    (hConcrete : BridgeOddConcreteSkewTarget) :
    ∀ {m : Nat}, 3 ≤ m → Odd m →
      Shared.CayleyHamiltonDecomposition 7 m :=
  shared_cayley_uniform_from_small3_and_bridge_odd_target
    (bridge_odd_certificate_target_of_concrete_skew_target hConcrete)

theorem shared_cayley_uniform_from_bridge_odd_concrete_return_target
    (hReturn : BridgeOddConcreteReturnTarget) :
    ∀ {m : Nat}, 3 ≤ m → Odd m →
      Shared.CayleyHamiltonDecomposition 7 m :=
  shared_cayley_uniform_from_small3_and_bridge_odd_target
    (bridge_odd_certificate_target_of_concrete_return_target hReturn)

theorem shared_cayley_uniform_from_bridge_odd_concrete_orbit_target
    (hOrbit : BridgeOddConcreteOrbitTarget) :
    ∀ {m : Nat}, 3 ≤ m → Odd m →
      Shared.CayleyHamiltonDecomposition 7 m :=
  shared_cayley_uniform_from_small3_and_bridge_odd_target
    (bridge_odd_certificate_target_of_concrete_orbit_target hOrbit)

end Additive4Plus2
end Handoff
end D7Odd
