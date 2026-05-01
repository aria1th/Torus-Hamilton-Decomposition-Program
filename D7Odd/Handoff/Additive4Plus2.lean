import D5Odd.Basic
import D7Odd.Handoff.ReturnCriterion

namespace D7Odd
namespace Handoff
namespace Additive4Plus2

abbrev Vec3 (m : Nat) := Fin 3 → ZMod m

def sum3 (m : Nat) (w : Vec3 m) : ZMod m :=
  Finset.univ.sum fun i : Fin 3 => w i

def Root3 (m : Nat) (w : Vec3 m) : Prop :=
  sum3 m w = 0

abbrev ARoot3 (m : Nat) := { w : Vec3 m // Root3 m w }

theorem sum3_vec (m : Nat) (w : Vec3 m) :
    sum3 m w = w 0 + w 1 + w 2 := by
  simp [sum3, Fin.sum_univ_three]

theorem sum5_vec (m : Nat) (w : D5Odd.Vec5 m) :
    D5Odd.sum5 m w = w 0 + w 1 + w 2 + w 3 + w 4 := by
  simp [D5Odd.sum5, Fin.sum_univ_succ, add_assoc]

theorem sum7_vec (m : Nat) (w : Vec7 m) :
    sum7 m w = w 0 + w 1 + w 2 + w 3 + w 4 + w 5 + w 6 := by
  simp [sum7, Fin.sum_univ_succ, add_assoc]

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

end Additive4Plus2
end Handoff
end D7Odd
