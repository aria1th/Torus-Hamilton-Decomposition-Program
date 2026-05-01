import D5Odd.Basic
import D7Odd.Handoff.ReturnCriterion
import Shared.AdditiveBridge

namespace D7Odd
namespace Handoff
namespace Additive4Plus2

abbrev Vec3 (m : Nat) := Fin 3 → ZMod m

def sum3 (m : Nat) (w : Vec3 m) : ZMod m :=
  Finset.univ.sum fun i : Fin 3 => w i

def Root3 (m : Nat) (w : Vec3 m) : Prop :=
  sum3 m w = 0

abbrev ARoot3 (m : Nat) := { w : Vec3 m // Root3 m w }

abbrev Direction3 := Fin 3

theorem sum3_vec (m : Nat) (w : Vec3 m) :
    sum3 m w = w 0 + w 1 + w 2 := by
  simp [sum3, Fin.sum_univ_three]

theorem sum5_vec (m : Nat) (w : D5Odd.Vec5 m) :
    D5Odd.sum5 m w = w 0 + w 1 + w 2 + w 3 + w 4 := by
  simp [D5Odd.sum5, Fin.sum_univ_succ, add_assoc]

theorem sum7_vec (m : Nat) (w : Vec7 m) :
    sum7 m w = w 0 + w 1 + w 2 + w 3 + w 4 + w 5 + w 6 := by
  simp [sum7, Fin.sum_univ_succ, add_assoc]

def e3 (m : Nat) (i : Direction3) : Vec3 m :=
  fun j => if j = i then 1 else 0

def q3 (m : Nat) (i : Direction3) : Vec3 m :=
  e3 m i - e3 m 2

theorem sum3_e3 (m : Nat) (i : Direction3) :
    sum3 m (e3 m i) = 1 := by
  simp [sum3, e3]

theorem sum3_add (m : Nat) (x y : Vec3 m) :
    sum3 m (x + y) = sum3 m x + sum3 m y := by
  simp [sum3, Finset.sum_add_distrib]

theorem sum3_q3 (m : Nat) (i : Direction3) :
    sum3 m (q3 m i) = 0 := by
  calc
    sum3 m (q3 m i) = sum3 m (e3 m i) - sum3 m (e3 m 2) := by
      simp [q3, sum3, Pi.sub_apply, Finset.sum_sub_distrib]
    _ = 0 := by
      rw [sum3_e3, sum3_e3]
      simp

theorem root3_add_q3 {m : Nat} {w : Vec3 m}
    (hw : Root3 m w) (i : Direction3) :
    Root3 m (w + q3 m i) := by
  unfold Root3 at hw ⊢
  rw [sum3_add, hw, sum3_q3]
  simp

def vec3OfPrefix {m : Nat} (x y : ZMod m) : ARoot3 m :=
  ⟨![x, y, -(x + y)], by
    unfold Root3
    simp [sum3_vec]⟩

def vec5OfPrefix {m : Nat}
    (x0 x1 x2 x3 : ZMod m) : D5Odd.ARoot5 m :=
  ⟨![x0, x1, x2, x3, -(x0 + x1 + x2 + x3)], by
    unfold D5Odd.Root5
    simp [sum5_vec]⟩

def targetVec {m : Nat} (base : D5Odd.ARoot5 m) (fiber : ARoot3 m) :
    Vec7 m :=
  ![base.1 0, base.1 1, base.1 2, base.1 3,
    fiber.1 0, fiber.1 1, base.1 4 + fiber.1 2]

theorem targetVec_root {m : Nat}
    (base : D5Odd.ARoot5 m) (fiber : ARoot3 m) :
    Root7 m (targetVec base fiber) := by
  unfold Root7
  rw [sum7_vec, show targetVec base fiber 0 = base.1 0 by rfl,
    show targetVec base fiber 1 = base.1 1 by rfl,
    show targetVec base fiber 2 = base.1 2 by rfl,
    show targetVec base fiber 3 = base.1 3 by rfl,
    show targetVec base fiber 4 = fiber.1 0 by rfl,
    show targetVec base fiber 5 = fiber.1 1 by rfl,
    show targetVec base fiber 6 = base.1 4 + fiber.1 2 by rfl]
  have hbase :
      base.1 0 + base.1 1 + base.1 2 + base.1 3 + base.1 4 = 0 := by
    simpa [D5Odd.Root5, sum5_vec] using base.2
  have hfiber : fiber.1 0 + fiber.1 1 + fiber.1 2 = 0 := by
    simpa [Root3, sum3_vec] using fiber.2
  linear_combination hbase + hfiber

def targetRoot {m : Nat} (base : D5Odd.ARoot5 m) (fiber : ARoot3 m) :
    RootState7 m :=
  ⟨targetVec base fiber, targetVec_root base fiber⟩

def baseAddQ {m : Nat} (i : D5Odd.Direction) (w : D5Odd.ARoot5 m) :
    D5Odd.ARoot5 m :=
  match i.val with
  | 0 => vec5OfPrefix (w.1 0 + 1) (w.1 1) (w.1 2) (w.1 3)
  | 1 => vec5OfPrefix (w.1 0) (w.1 1 + 1) (w.1 2) (w.1 3)
  | 2 => vec5OfPrefix (w.1 0) (w.1 1) (w.1 2 + 1) (w.1 3)
  | 3 => vec5OfPrefix (w.1 0) (w.1 1) (w.1 2) (w.1 3 + 1)
  | _ => w

def fiberAddQ {m : Nat} (i : Direction3) (w : ARoot3 m) : ARoot3 m :=
  match i.val with
  | 0 => vec3OfPrefix (w.1 0 + 1) (w.1 1)
  | 1 => vec3OfPrefix (w.1 0) (w.1 1 + 1)
  | _ => w

def baseDirectionOfSlot (i : Direction) : D5Odd.Direction :=
  match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 4

def fiberDirectionOfSlot (i : Direction) : Direction3 :=
  match i.val with
  | 4 => 0
  | 5 => 1
  | _ => 2

def baseRoot {m : Nat} (w : RootState7 m) : D5Odd.ARoot5 m :=
  vec5OfPrefix (w.1 0) (w.1 1) (w.1 2) (w.1 3)

def fiberRoot {m : Nat} (w : RootState7 m) : ARoot3 m :=
  vec3OfPrefix (w.1 4) (w.1 5)

theorem root5_sink_eq {m : Nat} (w : D5Odd.ARoot5 m) :
    w.1 4 = -(w.1 0 + w.1 1 + w.1 2 + w.1 3) := by
  have hsum :
      w.1 0 + w.1 1 + w.1 2 + w.1 3 + w.1 4 = 0 := by
    simpa [D5Odd.Root5, sum5_vec] using w.2
  calc
    w.1 4 = 0 - (w.1 0 + w.1 1 + w.1 2 + w.1 3) := by
      rw [← hsum]
      ring
    _ = -(w.1 0 + w.1 1 + w.1 2 + w.1 3) := by
      ring

theorem root3_sink_eq {m : Nat} (w : ARoot3 m) :
    w.1 2 = -(w.1 0 + w.1 1) := by
  have hsum : w.1 0 + w.1 1 + w.1 2 = 0 := by
    simpa [Root3, sum3_vec] using w.2
  calc
    w.1 2 = 0 - (w.1 0 + w.1 1) := by
      rw [← hsum]
      ring
    _ = -(w.1 0 + w.1 1) := by
      ring

def pairOfRoot3 {m : Nat} (w : ARoot3 m) : Fin 2 → ZMod m :=
  fun i => if i = 0 then w.1 0 else w.1 1

set_option linter.flexible false in
theorem vec3OfPrefix_pairOfRoot3 {m : Nat} (w : ARoot3 m) :
    vec3OfPrefix (pairOfRoot3 w 0) (pairOfRoot3 w 1) = w := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [pairOfRoot3, vec3OfPrefix]
  rw [root3_sink_eq]
  ring

def root3PairEquiv (m : Nat) :
    (Fin 2 → ZMod m) ≃ ARoot3 m where
  toFun p := vec3OfPrefix (p 0) (p 1)
  invFun := pairOfRoot3
  left_inv := by
    intro p
    ext i
    fin_cases i <;> simp [pairOfRoot3, vec3OfPrefix]
  right_inv := vec3OfPrefix_pairOfRoot3

noncomputable instance instFintypeARoot3 (m : Nat) [NeZero m] : Fintype (ARoot3 m) :=
  Fintype.ofEquiv (Fin 2 → ZMod m) (root3PairEquiv m)

theorem card_ARoot3 {m : Nat} [NeZero m] :
    Fintype.card (ARoot3 m) = m ^ 2 := by
  have hcard :
      Fintype.card (Fin 2 → ZMod m) = Fintype.card (ARoot3 m) :=
    Fintype.card_congr (root3PairEquiv m)
  calc
    Fintype.card (ARoot3 m) = Fintype.card (Fin 2 → ZMod m) := hcard.symm
    _ = Fintype.card (ZMod m) ^ 2 := by
      simp
    _ = m ^ 2 := by
      rw [ZMod.card]

theorem root7_sink_eq {m : Nat} (w : RootState7 m) :
    w.1 6 = -(w.1 0 + w.1 1 + w.1 2 + w.1 3 + w.1 4 + w.1 5) := by
  have hsum :
      w.1 0 + w.1 1 + w.1 2 + w.1 3 + w.1 4 + w.1 5 + w.1 6 = 0 := by
    simpa [Root7, sum7_vec] using w.2
  calc
    w.1 6 =
        0 - (w.1 0 + w.1 1 + w.1 2 + w.1 3 + w.1 4 + w.1 5) := by
      rw [← hsum]
      ring
    _ = -(w.1 0 + w.1 1 + w.1 2 + w.1 3 + w.1 4 + w.1 5) := by
      ring

set_option linter.flexible false in
theorem baseRoot_targetRoot {m : Nat}
    (base : D5Odd.ARoot5 m) (fiber : ARoot3 m) :
    baseRoot (targetRoot base fiber) = base := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [baseRoot, targetRoot, targetVec, vec5OfPrefix]
  · rw [root5_sink_eq]
    ring

set_option linter.flexible false in
theorem fiberRoot_targetRoot {m : Nat}
    (base : D5Odd.ARoot5 m) (fiber : ARoot3 m) :
    fiberRoot (targetRoot base fiber) = fiber := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [fiberRoot, targetRoot, targetVec, vec3OfPrefix]
  · rw [root3_sink_eq]
    ring

set_option linter.flexible false in
theorem targetRoot_base_fiber {m : Nat} (w : RootState7 m) :
    targetRoot (baseRoot w) (fiberRoot w) = w := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [targetRoot, targetVec, baseRoot, fiberRoot,
    vec5OfPrefix, vec3OfPrefix]
  · rw [root7_sink_eq]
    ring

def rootEquiv (m : Nat) :
    D5Odd.ARoot5 m × ARoot3 m ≃ RootState7 m where
  toFun bf := targetRoot bf.1 bf.2
  invFun w := (baseRoot w, fiberRoot w)
  left_inv := by
    intro bf
    rcases bf with ⟨base, fiber⟩
    simp [baseRoot_targetRoot, fiberRoot_targetRoot]
  right_inv := targetRoot_base_fiber

set_option linter.flexible false in
theorem baseRoot_addQRoot {m : Nat}
    (i : Direction) (w : RootState7 m) :
    baseRoot (addQRoot m i w) =
      baseAddQ (baseDirectionOfSlot i) (baseRoot w) := by
  apply Subtype.ext
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [baseRoot, addQRoot, addQ, q7, e7, vec5OfPrefix, baseAddQ,
      baseDirectionOfSlot]

set_option linter.flexible false in
theorem fiberRoot_addQRoot {m : Nat}
    (i : Direction) (w : RootState7 m) :
    fiberRoot (addQRoot m i w) =
      fiberAddQ (fiberDirectionOfSlot i) (fiberRoot w) := by
  apply Subtype.ext
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [fiberRoot, addQRoot, addQ, q7, e7, vec3OfPrefix, fiberAddQ,
      fiberDirectionOfSlot]

theorem rootEquiv_symm_addQRoot {m : Nat}
    (i : Direction) (w : RootState7 m) :
    (rootEquiv m).symm (addQRoot m i w) =
      (baseAddQ (baseDirectionOfSlot i) (baseRoot w),
        fiberAddQ (fiberDirectionOfSlot i) (fiberRoot w)) := by
  ext <;>
    simp [rootEquiv, baseRoot_addQRoot, fiberRoot_addQRoot]

abbrev ProductRoot (m : Nat) := D5Odd.ARoot5 m × ARoot3 m

def productStep {m : Nat} (i : Direction) : ProductRoot m → ProductRoot m :=
  fun bf =>
    (baseAddQ (baseDirectionOfSlot i) bf.1,
      fiberAddQ (fiberDirectionOfSlot i) bf.2)

theorem rootEquiv_symm_addQRoot_rootEquiv {m : Nat}
    (i : Direction) (bf : ProductRoot m) :
    (rootEquiv m).symm (addQRoot m i ((rootEquiv m) bf)) =
      productStep i bf := by
  rcases bf with ⟨base, fiber⟩
  rw [rootEquiv_symm_addQRoot]
  simp [productStep, rootEquiv, baseRoot_targetRoot, fiberRoot_targetRoot]

theorem productStep_bijective {m : Nat} (i : Direction) :
    Function.Bijective (productStep (m := m) i) := by
  have h :
      productStep (m := m) i =
        fun bf : ProductRoot m =>
          (rootEquiv m).symm (addQRoot m i ((rootEquiv m) bf)) := by
    funext bf
    exact (rootEquiv_symm_addQRoot_rootEquiv i bf).symm
  rw [h]
  exact (rootEquiv m).symm.bijective.comp
    ((addQRoot_bijective (m := m) i).comp (rootEquiv m).bijective)

def productLayerMap {m : Nat} (S : RootFlatSchedule m)
    (t : ZMod m) (c : Color) : ProductRoot m → ProductRoot m :=
  fun bf => productStep (S.dir t ((rootEquiv m) bf) c) bf

theorem rootEquiv_symm_layerMap {m : Nat} (S : RootFlatSchedule m)
    (t : ZMod m) (c : Color) (bf : ProductRoot m) :
    (rootEquiv m).symm (S.layerMap t c ((rootEquiv m) bf)) =
      productLayerMap S t c bf := by
  simp [RootFlatSchedule.layerMap, productLayerMap,
    rootEquiv_symm_addQRoot_rootEquiv]

theorem layerMap_bijective_of_productLayerMap_bijective {m : Nat}
    (S : RootFlatSchedule m) (t : ZMod m) (c : Color)
    (h : Function.Bijective (productLayerMap S t c)) :
    Function.Bijective (S.layerMap t c) := by
  exact Shared.bijective_of_equiv_conj
    (e := rootEquiv m) (f := S.layerMap t c)
    (g := productLayerMap S t c) h
    (rootEquiv_symm_layerMap S t c)

theorem layerBijective_of_productLayerMaps {m : Nat}
    (S : RootFlatSchedule m)
    (h : ∀ t c, Function.Bijective (productLayerMap S t c)) :
    S.layerBijective := by
  intro t c
  exact layerMap_bijective_of_productLayerMap_bijective S t c (h t c)

structure ProductRootSchedule (m : Nat) where
  dir : ZMod m → ProductRoot m → Color → Direction

namespace ProductRootSchedule

def rowLatin {m : Nat} (P : ProductRootSchedule m) : Prop :=
  ∀ t bf, Function.Bijective fun c : Color => P.dir t bf c

def layerMap {m : Nat} (P : ProductRootSchedule m)
    (t : ZMod m) (c : Color) : ProductRoot m → ProductRoot m :=
  fun bf => productStep (P.dir t bf c) bf

def layerBijective {m : Nat} (P : ProductRootSchedule m) : Prop :=
  ∀ t c, Function.Bijective (P.layerMap t c)

def returnMap {m : Nat} [NeZero m]
    (P : ProductRootSchedule m) (c : Color) :
    ProductRoot m → ProductRoot m :=
  fun bf => ((List.range m).foldl
    (fun x (t : Nat) => P.layerMap (t : ZMod m) c x) bf)

def returnsSingleCycle {m : Nat} [NeZero m]
    (P : ProductRootSchedule m) : Prop :=
  ∀ c : Color, IsSingleCycleMap (P.returnMap c)

theorem rowLatin_of_stateDirectionPermutation {m : Nat}
    (P : ProductRootSchedule m)
    (rawDir : ZMod m → ProductRoot m → Color → Direction)
    (kappa : ZMod m → ProductRoot m → Direction → Direction)
    (hdir : ∀ t bf, Function.Bijective (rawDir t bf))
    (hkappa : ∀ t bf, Function.Bijective (kappa t bf))
    (hP : ∀ t bf c, P.dir t bf c = kappa t bf (rawDir t bf c)) :
    P.rowLatin := by
  intro t bf
  have hcomp :
      Function.Bijective
        (fun c : Color => kappa t bf (rawDir t bf c)) :=
    Shared.composeRowDirection_bijective
      (rawDir t bf) (kappa t bf) (hdir t bf) (hkappa t bf)
  convert hcomp using 1
  funext c
  exact hP t bf c

theorem layerMap_eq_skewProductMap_of_components {m : Nat}
    (P : ProductRootSchedule m)
    (baseStep :
      ZMod m → Color → D5Odd.ARoot5 m → D5Odd.ARoot5 m)
    (fiberStep :
      ZMod m → Color → D5Odd.ARoot5 m → ARoot3 m → ARoot3 m)
    (hbase : ∀ t c base fiber,
      baseAddQ (baseDirectionOfSlot (P.dir t (base, fiber) c)) base =
        baseStep t c base)
    (hfiber : ∀ t c base fiber,
      fiberAddQ (fiberDirectionOfSlot (P.dir t (base, fiber) c)) fiber =
        fiberStep t c base fiber)
    (t : ZMod m) (c : Color) :
    P.layerMap t c = Shared.skewProductMap (baseStep t c) (fiberStep t c) := by
  funext bf
  rcases bf with ⟨base, fiber⟩
  exact Prod.ext (hbase t c base fiber) (hfiber t c base fiber)

theorem layerBijective_of_skewProductComponents {m : Nat}
    (P : ProductRootSchedule m)
    (baseStep :
      ZMod m → Color → D5Odd.ARoot5 m → D5Odd.ARoot5 m)
    (fiberStep :
      ZMod m → Color → D5Odd.ARoot5 m → ARoot3 m → ARoot3 m)
    (hbaseEq : ∀ t c base fiber,
      baseAddQ (baseDirectionOfSlot (P.dir t (base, fiber) c)) base =
        baseStep t c base)
    (hfiberEq : ∀ t c base fiber,
      fiberAddQ (fiberDirectionOfSlot (P.dir t (base, fiber) c)) fiber =
        fiberStep t c base fiber)
    (hbaseBij : ∀ t c, Function.Bijective (baseStep t c))
    (hfiberBij : ∀ t c base, Function.Bijective (fiberStep t c base)) :
    P.layerBijective := by
  intro t c
  rw [P.layerMap_eq_skewProductMap_of_components
    baseStep fiberStep hbaseEq hfiberEq t c]
  exact Shared.skewProductMap_bijective
    (baseStep t c) (fiberStep t c) (hbaseBij t c) (hfiberBij t c)

theorem returnSingleCycle_of_skewReturn {m : Nat} [NeZero m]
    (P : ProductRootSchedule m) (c : Color)
    (baseReturn : D5Odd.ARoot5 m → D5Odd.ARoot5 m)
    (fiberReturn : D5Odd.ARoot5 m → ARoot3 m → ARoot3 m)
    (base : D5Odd.ARoot5 m) (period : Nat)
    (hReturn : ∀ bf : ProductRoot m,
      P.returnMap c bf = Shared.skewProductMap baseReturn fiberReturn bf)
    (hbase : Function.Bijective baseReturn)
    (hfiber : ∀ u, Function.Bijective (fiberReturn u))
    (hreturnBase : (baseReturn^[period]) base = base)
    (hbaseCover : ∀ b, ∃ k : Nat,
      k < period ∧ (baseReturn^[k]) base = b)
    (hmonodromy :
      IsSingleCycleMap
        (Shared.sectionReturn
          (Shared.skewProductMap baseReturn fiberReturn) base period)) :
    IsSingleCycleMap (P.returnMap c) := by
  have hmonoShared :
      Shared.IsSingleCycleMap
        (Shared.sectionReturn
          (Shared.skewProductMap baseReturn fiberReturn) base period) := by
    simpa [Shared.IsSingleCycleMap, IsSingleCycleMap] using hmonodromy
  have hcycleShared :
      Shared.IsSingleCycleMap
        (Shared.skewProductMap baseReturn fiberReturn) :=
    Shared.single_cycle_of_skewProduct_base_orbit_monodromy
      baseReturn fiberReturn base period hbase hfiber hreturnBase hbaseCover
      hmonoShared
  have hReturnFun :
      P.returnMap c = Shared.skewProductMap baseReturn fiberReturn := by
    funext bf
    exact hReturn bf
  rw [hReturnFun]
  simpa [Shared.IsSingleCycleMap, IsSingleCycleMap] using hcycleShared

theorem returnsSingleCycle_of_skewReturns {m : Nat} [NeZero m]
    (P : ProductRootSchedule m)
    (baseReturn : Color → D5Odd.ARoot5 m → D5Odd.ARoot5 m)
    (fiberReturn : Color → D5Odd.ARoot5 m → ARoot3 m → ARoot3 m)
    (base : Color → D5Odd.ARoot5 m) (period : Color → Nat)
    (hReturn : ∀ c bf,
      P.returnMap c bf =
        Shared.skewProductMap (baseReturn c) (fiberReturn c) bf)
    (hbase : ∀ c, Function.Bijective (baseReturn c))
    (hfiber : ∀ c u, Function.Bijective (fiberReturn c u))
    (hreturnBase : ∀ c, ((baseReturn c)^[period c]) (base c) = base c)
    (hbaseCover : ∀ c b, ∃ k : Nat,
      k < period c ∧ ((baseReturn c)^[k]) (base c) = b)
    (hmonodromy : ∀ c,
      IsSingleCycleMap
        (Shared.sectionReturn
          (Shared.skewProductMap (baseReturn c) (fiberReturn c))
          (base c) (period c))) :
    P.returnsSingleCycle := by
  intro c
  exact P.returnSingleCycle_of_skewReturn c
    (baseReturn c) (fiberReturn c) (base c) (period c)
    (hReturn c) (hbase c) (hfiber c) (hreturnBase c)
    (hbaseCover c) (hmonodromy c)

def toRootFlatSchedule {m : Nat} (P : ProductRootSchedule m) :
    RootFlatSchedule m where
  dir := fun t w c => P.dir t ((rootEquiv m).symm w) c

theorem toRootFlatSchedule_rowLatin {m : Nat}
    (P : ProductRootSchedule m) :
    P.toRootFlatSchedule.rowLatin ↔ P.rowLatin := by
  constructor
  · intro h t bf
    simpa [toRootFlatSchedule] using h t ((rootEquiv m) bf)
  · intro h t w
    exact h t ((rootEquiv m).symm w)

theorem toRootFlatSchedule_layerMap_conj {m : Nat}
    (P : ProductRootSchedule m) (t : ZMod m) (c : Color)
    (bf : ProductRoot m) :
    (rootEquiv m).symm
        (P.toRootFlatSchedule.layerMap t c ((rootEquiv m) bf)) =
      P.layerMap t c bf := by
  simp [toRootFlatSchedule, RootFlatSchedule.layerMap, layerMap,
    rootEquiv_symm_addQRoot_rootEquiv]

theorem toRootFlatSchedule_layerBijective {m : Nat}
    (P : ProductRootSchedule m) (h : P.layerBijective) :
    P.toRootFlatSchedule.layerBijective := by
  intro t c
  exact Shared.bijective_of_equiv_conj
    (e := rootEquiv m) (f := P.toRootFlatSchedule.layerMap t c)
    (g := P.layerMap t c) (h t c)
    (P.toRootFlatSchedule_layerMap_conj t c)

theorem toRootFlatSchedule_returnMap_conj
    {m : Nat} [NeZero m] (P : ProductRootSchedule m)
    (c : Color) (bf : ProductRoot m) :
    (rootEquiv m).symm
        (P.toRootFlatSchedule.returnMap c ((rootEquiv m) bf)) =
      P.returnMap c bf := by
  unfold RootFlatSchedule.returnMap returnMap
  let F : RootState7 m → Nat → RootState7 m :=
    fun w (t : Nat) => P.toRootFlatSchedule.layerMap (t : ZMod m) c w
  let G : ProductRoot m → Nat → ProductRoot m :=
    fun bf (t : Nat) => P.layerMap (t : ZMod m) c bf
  have hfold :
      ∀ ts : List Nat, ∀ bf : ProductRoot m,
        (rootEquiv m).symm (ts.foldl F ((rootEquiv m) bf)) =
          ts.foldl G bf := by
    intro ts
    induction ts with
    | nil =>
        intro bf
        simp [F, G]
    | cons t ts ih =>
        intro bf
        rw [List.foldl_cons, List.foldl_cons]
        have hstep :
            F ((rootEquiv m) bf) t = (rootEquiv m) (G bf t) := by
          simp only [F, G]
          apply (rootEquiv m).symm.injective
          simpa using P.toRootFlatSchedule_layerMap_conj (t : ZMod m) c bf
        rw [hstep]
        exact ih (G bf t)
  simpa [F, G] using hfold (List.range m) bf

theorem toRootFlatSchedule_returnsSingleCycle
    {m : Nat} [NeZero m] (P : ProductRootSchedule m)
    (h : P.returnsSingleCycle) :
    P.toRootFlatSchedule.returnsSingleCycle := by
  intro c
  have hShared : Shared.IsSingleCycleMap (P.returnMap c) := by
    simpa [Shared.IsSingleCycleMap, IsSingleCycleMap] using h c
  have hCycle :=
    Shared.single_cycle_of_equiv_conj
      (e := rootEquiv m)
      (f := P.toRootFlatSchedule.returnMap c)
      (g := P.returnMap c)
      hShared
      (P.toRootFlatSchedule_returnMap_conj c)
  simpa [Shared.IsSingleCycleMap, IsSingleCycleMap] using hCycle

end ProductRootSchedule

structure ProductRootCertificate (m : Nat) [NeZero m] where
  schedule : ProductRootSchedule m
  rowLatin : schedule.rowLatin
  layerBijective : schedule.layerBijective
  returnsSingleCycle : schedule.returnsSingleCycle

def ProductRootCertificate.ofLocalBridgeAndSkewReturns
    {m : Nat} [NeZero m]
    (P : ProductRootSchedule m)
    (rawDir : ZMod m → ProductRoot m → Color → Direction)
    (kappa : ZMod m → ProductRoot m → Direction → Direction)
    (baseStep :
      ZMod m → Color → D5Odd.ARoot5 m → D5Odd.ARoot5 m)
    (fiberStep :
      ZMod m → Color → D5Odd.ARoot5 m → ARoot3 m → ARoot3 m)
    (baseReturn : Color → D5Odd.ARoot5 m → D5Odd.ARoot5 m)
    (fiberReturn : Color → D5Odd.ARoot5 m → ARoot3 m → ARoot3 m)
    (base : Color → D5Odd.ARoot5 m) (period : Color → Nat)
    (hdir : ∀ t bf, Function.Bijective (rawDir t bf))
    (hkappa : ∀ t bf, Function.Bijective (kappa t bf))
    (hP : ∀ t bf c, P.dir t bf c = kappa t bf (rawDir t bf c))
    (hbaseLayer : ∀ t c base fiber,
      baseAddQ (baseDirectionOfSlot (P.dir t (base, fiber) c)) base =
        baseStep t c base)
    (hfiberLayer : ∀ t c base fiber,
      fiberAddQ (fiberDirectionOfSlot (P.dir t (base, fiber) c)) fiber =
        fiberStep t c base fiber)
    (hbaseLayerBij : ∀ t c, Function.Bijective (baseStep t c))
    (hfiberLayerBij : ∀ t c base, Function.Bijective (fiberStep t c base))
    (hReturn : ∀ c bf,
      P.returnMap c bf =
        Shared.skewProductMap (baseReturn c) (fiberReturn c) bf)
    (hbaseReturnBij : ∀ c, Function.Bijective (baseReturn c))
    (hfiberReturnBij : ∀ c u, Function.Bijective (fiberReturn c u))
    (hreturnBase : ∀ c, ((baseReturn c)^[period c]) (base c) = base c)
    (hbaseCover : ∀ c b, ∃ k : Nat,
      k < period c ∧ ((baseReturn c)^[k]) (base c) = b)
    (hmonodromy : ∀ c,
      IsSingleCycleMap
        (Shared.sectionReturn
          (Shared.skewProductMap (baseReturn c) (fiberReturn c))
          (base c) (period c))) :
    ProductRootCertificate m where
  schedule := P
  rowLatin :=
    P.rowLatin_of_stateDirectionPermutation rawDir kappa hdir hkappa hP
  layerBijective :=
    P.layerBijective_of_skewProductComponents
      baseStep fiberStep hbaseLayer hfiberLayer hbaseLayerBij
      hfiberLayerBij
  returnsSingleCycle :=
    P.returnsSingleCycle_of_skewReturns
      baseReturn fiberReturn base period hReturn hbaseReturnBij
      hfiberReturnBij hreturnBase hbaseCover hmonodromy

def ProductRootCertificate.toRootFlatCertificate
    {m : Nat} [NeZero m] (cert : ProductRootCertificate m) :
    RootFlatCertificate m where
  schedule := cert.schedule.toRootFlatSchedule
  rowLatin := (ProductRootSchedule.toRootFlatSchedule_rowLatin cert.schedule).2
    cert.rowLatin
  layerBijective :=
    ProductRootSchedule.toRootFlatSchedule_layerBijective cert.schedule
      cert.layerBijective
  returnsSingleCycle :=
    ProductRootSchedule.toRootFlatSchedule_returnsSingleCycle cert.schedule
      cert.returnsSingleCycle

theorem ProductRootCertificate.toHamiltonDecompositionD7
    {m : Nat} [NeZero m] (cert : ProductRootCertificate m) :
    HamiltonDecompositionD7 m :=
  certificate_implies_hamilton cert.toRootFlatCertificate

theorem ProductRootCertificate.toSharedLayeredHamilton
    {m : Nat} [NeZero m] (cert : ProductRootCertificate m) :
    Shared.RootFlatLayeredHamiltonDecomposition
      Color Direction (RootState7 m) m :=
  cert.toRootFlatCertificate.toSharedLayeredHamilton

end Additive4Plus2
end Handoff
end D7Odd
