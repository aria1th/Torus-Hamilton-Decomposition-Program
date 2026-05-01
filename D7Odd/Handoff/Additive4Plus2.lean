import D5Odd.Basic
import D7Odd.Handoff.ReturnCriterion
import Shared.Monodromy

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

end ProductRootSchedule

structure ProductRootCertificate (m : Nat) [NeZero m] where
  schedule : ProductRootSchedule m
  rowLatin : schedule.rowLatin
  layerBijective : schedule.layerBijective
  returnsSingleCycle : schedule.toRootFlatSchedule.returnsSingleCycle

def ProductRootCertificate.toRootFlatCertificate
    {m : Nat} [NeZero m] (cert : ProductRootCertificate m) :
    RootFlatCertificate m where
  schedule := cert.schedule.toRootFlatSchedule
  rowLatin := (ProductRootSchedule.toRootFlatSchedule_rowLatin cert.schedule).2
    cert.rowLatin
  layerBijective :=
    ProductRootSchedule.toRootFlatSchedule_layerBijective cert.schedule
      cert.layerBijective
  returnsSingleCycle := cert.returnsSingleCycle

end Additive4Plus2
end Handoff
end D7Odd
