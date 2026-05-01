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

theorem rankStep_return_self
    {α : Type*} {N : Nat} [NeZero N]
    (f : α → α) (rank : α → ZMod N)
    (hrank : Function.Bijective rank)
    (hstep : ∀ x, rank (f x) = rank x + 1)
    (x : α) :
    (f^[N]) x = x := by
  apply hrank.1
  calc
    rank ((f^[N]) x) = rank x + (N : ZMod N) :=
      iterate_rank_add_one f rank hstep N x
    _ = rank x := by simp

theorem rankStep_orbit_cover
    {α : Type*} {N : Nat} [NeZero N]
    (f : α → α) (rank : α → ZMod N)
    (hrank : Function.Bijective rank)
    (hstep : ∀ x, rank (f x) = rank x + 1)
    (x y : α) :
    ∃ k : Nat, k < N ∧ (f^[k]) x = y := by
  let delta : ZMod N := rank y - rank x
  refine ⟨delta.val, ZMod.val_lt delta, ?_⟩
  apply hrank.1
  calc
    rank ((f^[delta.val]) x) =
        rank x + (delta.val : ZMod N) :=
      iterate_rank_add_one f rank hstep delta.val x
    _ = rank x + delta := by rw [ZMod.natCast_zmod_val]
    _ = rank y := by ring

structure BridgeConcreteRankPackage (m : Nat) [NeZero m] where
  row : Color → ZMod m → Direction
  fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m
  perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3
  basePoint : Color → D5Odd.ARoot5 m
  period : Color → Nat
  rank : (c : Color) → D5Odd.ARoot5 m → ZMod (period c)
  hrow : ∀ t, Function.Bijective fun c : Color => row c t
  hperm : ∀ t base, Function.Bijective (perm t base)
  hperiod : ∀ c, 0 < period c
  hrank : ∀ c, Function.Bijective (rank c)
  hbaseStep : ∀ c base,
    rank c (bridgeConcreteBaseReturn row c base) = rank c base + 1
  hmonodromy : ∀ c,
    IsSingleCycleMap
      (Shared.sectionReturn
        (Shared.skewProductMap
          (bridgeConcreteBaseReturn row c)
          (bridgeConcreteFiberReturn row fiberLayer perm c))
        (basePoint c) (period c))

def BridgeConcreteRankPackage.toConcreteOrbitPackage
    {m : Nat} [NeZero m] (pkg : BridgeConcreteRankPackage m) :
    BridgeConcreteOrbitPackage m where
  row := pkg.row
  fiberLayer := pkg.fiberLayer
  perm := pkg.perm
  basePoint := pkg.basePoint
  period := pkg.period
  hrow := pkg.hrow
  hperm := pkg.hperm
  hreturnBase := by
    intro c
    haveI : NeZero (pkg.period c) := ⟨ne_of_gt (pkg.hperiod c)⟩
    exact rankStep_return_self
      (bridgeConcreteBaseReturn pkg.row c)
      (pkg.rank c) (pkg.hrank c) (pkg.hbaseStep c) (pkg.basePoint c)
  hbaseCover := by
    intro c b
    haveI : NeZero (pkg.period c) := ⟨ne_of_gt (pkg.hperiod c)⟩
    exact rankStep_orbit_cover
      (bridgeConcreteBaseReturn pkg.row c)
      (pkg.rank c) (pkg.hrank c) (pkg.hbaseStep c) (pkg.basePoint c) b
  hmonodromy := pkg.hmonodromy

def BridgeConcreteRankPackage.toConcreteReturnPackage
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcreteRankPackage m) :
    BridgeConcreteReturnPackage m :=
  pkg.toConcreteOrbitPackage.toConcreteReturnPackage hm

def BridgeConcreteRankPackage.toConcreteSkewPackage
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcreteRankPackage m) :
    BridgeConcreteSkewPackage m :=
  (pkg.toConcreteOrbitPackage).toConcreteSkewPackage hm

def BridgeConcreteRankPackage.toLocalSkewPackage
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcreteRankPackage m) :
    BridgeLocalSkewPackage m :=
  (pkg.toConcreteOrbitPackage).toLocalSkewPackage hm

def BridgeConcreteRankPackage.toCertificate
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcreteRankPackage m) :
    BridgeProductRootCertificate m :=
  (pkg.toConcreteOrbitPackage).toCertificate hm

structure BridgeConcretePowRankPackage (m : Nat) [NeZero m] where
  row : Color → ZMod m → Direction
  fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m
  perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3
  basePoint : Color → D5Odd.ARoot5 m
  rank : Color → D5Odd.ARoot5 m → ZMod (m ^ 4)
  hrow : ∀ t, Function.Bijective fun c : Color => row c t
  hperm : ∀ t base, Function.Bijective (perm t base)
  hrank : ∀ c, Function.Bijective (rank c)
  hbaseStep : ∀ c base,
    rank c (bridgeConcreteBaseReturn row c base) = rank c base + 1
  hmonodromy : ∀ c,
    IsSingleCycleMap
      (Shared.sectionReturn
        (Shared.skewProductMap
          (bridgeConcreteBaseReturn row c)
          (bridgeConcreteFiberReturn row fiberLayer perm c))
        (basePoint c) (m ^ 4))

def BridgeConcretePowRankPackage.toConcreteRankPackage
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcretePowRankPackage m) :
    BridgeConcreteRankPackage m where
  row := pkg.row
  fiberLayer := pkg.fiberLayer
  perm := pkg.perm
  basePoint := pkg.basePoint
  period := fun _ => m ^ 4
  rank := pkg.rank
  hrow := pkg.hrow
  hperm := pkg.hperm
  hperiod := by
    intro _c
    have hmpos : 0 < m := by omega
    exact pow_pos hmpos 4
  hrank := pkg.hrank
  hbaseStep := pkg.hbaseStep
  hmonodromy := pkg.hmonodromy

def BridgeConcretePowRankPackage.toConcreteOrbitPackage
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcretePowRankPackage m) :
    BridgeConcreteOrbitPackage m :=
  (pkg.toConcreteRankPackage hm).toConcreteOrbitPackage

def BridgeConcretePowRankPackage.toConcreteReturnPackage
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcretePowRankPackage m) :
    BridgeConcreteReturnPackage m :=
  (pkg.toConcreteRankPackage hm).toConcreteReturnPackage hm

def BridgeConcretePowRankPackage.toConcreteSkewPackage
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcretePowRankPackage m) :
    BridgeConcreteSkewPackage m :=
  (pkg.toConcreteRankPackage hm).toConcreteSkewPackage hm

def BridgeConcretePowRankPackage.toLocalSkewPackage
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcretePowRankPackage m) :
    BridgeLocalSkewPackage m :=
  (pkg.toConcreteRankPackage hm).toLocalSkewPackage hm

def BridgeConcretePowRankPackage.toCertificate
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcretePowRankPackage m) :
    BridgeProductRootCertificate m :=
  (pkg.toConcreteRankPackage hm).toCertificate hm

theorem rankStep_single_cycle
    {α : Type*} {N : Nat} [NeZero N]
    (f : α → α) (rank : α → ZMod N)
    (hrank : Function.Bijective rank)
    (hstep : ∀ x, rank (f x) = rank x + 1) :
    IsSingleCycleMap f :=
  single_cycle_of_zmod_rank f rank hrank hstep

def bridgeConcreteSectionReturn {m : Nat}
    (row : Color → ZMod m → Direction)
    (fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m)
    (perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3)
    (c : Color) (basePoint : D5Odd.ARoot5 m) (period : Nat) :
    ARoot3 m → ARoot3 m :=
  Shared.sectionReturn
    (Shared.skewProductMap
      (bridgeConcreteBaseReturn row c)
      (bridgeConcreteFiberReturn row fiberLayer perm c))
    basePoint period

structure BridgeConcreteFullRankPackage (m : Nat) [NeZero m] where
  row : Color → ZMod m → Direction
  fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m
  perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3
  basePoint : Color → D5Odd.ARoot5 m
  baseRank : Color → D5Odd.ARoot5 m → ZMod (m ^ 4)
  fiberRank : Color → ARoot3 m → ZMod (m ^ 2)
  hrow : ∀ t, Function.Bijective fun c : Color => row c t
  hperm : ∀ t base, Function.Bijective (perm t base)
  hbaseRank : ∀ c, Function.Bijective (baseRank c)
  hbaseStep : ∀ c base,
    baseRank c (bridgeConcreteBaseReturn row c base) =
      baseRank c base + 1
  hfiberRank : ∀ c, Function.Bijective (fiberRank c)
  hfiberStep : ∀ c fiber,
    fiberRank c
        (bridgeConcreteSectionReturn row fiberLayer perm c
          (basePoint c) (m ^ 4) fiber) =
      fiberRank c fiber + 1

def BridgeConcreteFullRankPackage.toConcretePowRankPackage
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcreteFullRankPackage m) :
    BridgeConcretePowRankPackage m where
  row := pkg.row
  fiberLayer := pkg.fiberLayer
  perm := pkg.perm
  basePoint := pkg.basePoint
  rank := pkg.baseRank
  hrow := pkg.hrow
  hperm := pkg.hperm
  hrank := pkg.hbaseRank
  hbaseStep := pkg.hbaseStep
  hmonodromy := by
    intro c
    have hmpos : 0 < m := by omega
    haveI : NeZero (m ^ 2) := ⟨ne_of_gt (pow_pos hmpos 2)⟩
    exact rankStep_single_cycle
      (bridgeConcreteSectionReturn pkg.row pkg.fiberLayer pkg.perm c
        (pkg.basePoint c) (m ^ 4))
      (pkg.fiberRank c) (pkg.hfiberRank c) (pkg.hfiberStep c)

def BridgeConcreteFullRankPackage.toConcreteRankPackage
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcreteFullRankPackage m) :
    BridgeConcreteRankPackage m :=
  (pkg.toConcretePowRankPackage hm).toConcreteRankPackage hm

def BridgeConcreteFullRankPackage.toConcreteOrbitPackage
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcreteFullRankPackage m) :
    BridgeConcreteOrbitPackage m :=
  (pkg.toConcretePowRankPackage hm).toConcreteOrbitPackage hm

def BridgeConcreteFullRankPackage.toConcreteReturnPackage
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcreteFullRankPackage m) :
    BridgeConcreteReturnPackage m :=
  (pkg.toConcretePowRankPackage hm).toConcreteReturnPackage hm

def BridgeConcreteFullRankPackage.toConcreteSkewPackage
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcreteFullRankPackage m) :
    BridgeConcreteSkewPackage m :=
  (pkg.toConcretePowRankPackage hm).toConcreteSkewPackage hm

def BridgeConcreteFullRankPackage.toLocalSkewPackage
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcreteFullRankPackage m) :
    BridgeLocalSkewPackage m :=
  (pkg.toConcretePowRankPackage hm).toLocalSkewPackage hm

def BridgeConcreteFullRankPackage.toCertificate
    {m : Nat} [NeZero m] (hm : 5 ≤ m)
    (pkg : BridgeConcreteFullRankPackage m) :
    BridgeProductRootCertificate m :=
  (pkg.toConcretePowRankPackage hm).toCertificate hm

def BridgeOddConcreteSkewTarget : Type :=
  ∀ {m : Nat} [NeZero m], 5 ≤ m → Odd m → BridgeConcreteSkewPackage m

def BridgeOddConcreteReturnTarget : Type :=
  ∀ {m : Nat} [NeZero m], 5 ≤ m → Odd m → BridgeConcreteReturnPackage m

def BridgeOddConcreteOrbitTarget : Type :=
  ∀ {m : Nat} [NeZero m], 5 ≤ m → Odd m → BridgeConcreteOrbitPackage m

def BridgeOddConcreteRankTarget : Type :=
  ∀ {m : Nat} [NeZero m], 5 ≤ m → Odd m → BridgeConcreteRankPackage m

def BridgeOddConcretePowRankTarget : Type :=
  ∀ {m : Nat} [NeZero m], 5 ≤ m → Odd m → BridgeConcretePowRankPackage m

def BridgeOddConcreteFullRankTarget : Type :=
  ∀ {m : Nat} [NeZero m], 5 ≤ m → Odd m → BridgeConcreteFullRankPackage m

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

def bridge_odd_concrete_orbit_target_of_concrete_rank_target
    (hRank : BridgeOddConcreteRankTarget) :
    BridgeOddConcreteOrbitTarget :=
  fun hm hodd => (hRank hm hodd).toConcreteOrbitPackage

def bridge_odd_certificate_target_of_concrete_rank_target
    (hRank : BridgeOddConcreteRankTarget) :
    BridgeOddCertificateTarget :=
  bridge_odd_certificate_target_of_concrete_orbit_target
    (bridge_odd_concrete_orbit_target_of_concrete_rank_target hRank)

def bridge_odd_concrete_rank_target_of_concrete_pow_rank_target
    (hRank : BridgeOddConcretePowRankTarget) :
    BridgeOddConcreteRankTarget :=
  fun hm hodd => (hRank hm hodd).toConcreteRankPackage hm

def bridge_odd_certificate_target_of_concrete_pow_rank_target
    (hRank : BridgeOddConcretePowRankTarget) :
    BridgeOddCertificateTarget :=
  bridge_odd_certificate_target_of_concrete_rank_target
    (bridge_odd_concrete_rank_target_of_concrete_pow_rank_target hRank)

def bridge_odd_concrete_pow_rank_target_of_concrete_full_rank_target
    (hRank : BridgeOddConcreteFullRankTarget) :
    BridgeOddConcretePowRankTarget :=
  fun hm hodd => (hRank hm hodd).toConcretePowRankPackage hm

def bridge_odd_certificate_target_of_concrete_full_rank_target
    (hRank : BridgeOddConcreteFullRankTarget) :
    BridgeOddCertificateTarget :=
  bridge_odd_certificate_target_of_concrete_pow_rank_target
    (bridge_odd_concrete_pow_rank_target_of_concrete_full_rank_target hRank)

theorem torus_from_bridge_odd_concrete_full_rank_target
    (hRank : BridgeOddConcreteFullRankTarget)
    {m : Nat} [NeZero m] (hm3 : 3 ≤ m) (hodd : Odd m) :
    D7Odd.TorusHamiltonDecompositionD7 m :=
  torus_from_small3_and_bridge_odd_target
    (bridge_odd_certificate_target_of_concrete_full_rank_target hRank) hm3 hodd

theorem cayley_from_bridge_odd_concrete_full_rank_target
    (hRank : BridgeOddConcreteFullRankTarget)
    {m : Nat} [NeZero m] (hm3 : 3 ≤ m) (hodd : Odd m) :
    D7Odd.CayleyHamiltonDecompositionD7 m :=
  cayley_from_small3_and_bridge_odd_target
    (bridge_odd_certificate_target_of_concrete_full_rank_target hRank) hm3 hodd

theorem torus_uniform_from_bridge_odd_concrete_full_rank_target
    (hRank : BridgeOddConcreteFullRankTarget) :
    ∀ {m : Nat}, 3 ≤ m → Odd m →
      D7Odd.TorusHamiltonDecompositionD7 m := by
  intro m hm3 hodd
  haveI : NeZero m := ⟨by omega⟩
  exact torus_from_bridge_odd_concrete_full_rank_target hRank hm3 hodd

theorem cayley_uniform_from_bridge_odd_concrete_full_rank_target
    (hRank : BridgeOddConcreteFullRankTarget) :
    ∀ {m : Nat}, 3 ≤ m → Odd m →
      D7Odd.CayleyHamiltonDecompositionD7 m := by
  intro m hm3 hodd
  haveI : NeZero m := ⟨by omega⟩
  exact cayley_from_bridge_odd_concrete_full_rank_target hRank hm3 hodd

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

theorem shared_cayley_uniform_from_bridge_odd_concrete_rank_target
    (hRank : BridgeOddConcreteRankTarget) :
    ∀ {m : Nat}, 3 ≤ m → Odd m →
      Shared.CayleyHamiltonDecomposition 7 m :=
  shared_cayley_uniform_from_small3_and_bridge_odd_target
    (bridge_odd_certificate_target_of_concrete_rank_target hRank)

theorem shared_cayley_uniform_from_bridge_odd_concrete_pow_rank_target
    (hRank : BridgeOddConcretePowRankTarget) :
    ∀ {m : Nat}, 3 ≤ m → Odd m →
      Shared.CayleyHamiltonDecomposition 7 m :=
  shared_cayley_uniform_from_small3_and_bridge_odd_target
    (bridge_odd_certificate_target_of_concrete_pow_rank_target hRank)

theorem shared_cayley_uniform_from_bridge_odd_concrete_full_rank_target
    (hRank : BridgeOddConcreteFullRankTarget) :
    ∀ {m : Nat}, 3 ≤ m → Odd m →
      Shared.CayleyHamiltonDecomposition 7 m :=
  shared_cayley_uniform_from_small3_and_bridge_odd_target
    (bridge_odd_certificate_target_of_concrete_full_rank_target hRank)

end Additive4Plus2
end Handoff
end D7Odd
