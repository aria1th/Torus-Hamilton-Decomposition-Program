import D7Odd.Handoff.Additive4Plus2

namespace D7Odd
namespace Handoff
namespace Additive4Plus2

def bridgeTargetVec {m : Nat} (base : D5Odd.ARoot5 m) (fiber : ARoot3 m) :
    Vec7 m :=
  ![base.1 0, base.1 1, base.1 2, base.1 3,
    fiber.1 0 - (base.1 0 + base.1 1 + base.1 2 + base.1 3),
    fiber.1 1, fiber.1 2]

theorem bridgeTargetVec_root {m : Nat}
    (base : D5Odd.ARoot5 m) (fiber : ARoot3 m) :
    Root7 m (bridgeTargetVec base fiber) := by
  unfold Root7
  rw [sum7_vec, show bridgeTargetVec base fiber 0 = base.1 0 by rfl,
    show bridgeTargetVec base fiber 1 = base.1 1 by rfl,
    show bridgeTargetVec base fiber 2 = base.1 2 by rfl,
    show bridgeTargetVec base fiber 3 = base.1 3 by rfl,
    show bridgeTargetVec base fiber 4 =
      fiber.1 0 - (base.1 0 + base.1 1 + base.1 2 + base.1 3) by rfl,
    show bridgeTargetVec base fiber 5 = fiber.1 1 by rfl,
    show bridgeTargetVec base fiber 6 = fiber.1 2 by rfl]
  have hfiber : fiber.1 0 + fiber.1 1 + fiber.1 2 = 0 := by
    simpa [Root3, sum3_vec] using fiber.2
  linear_combination hfiber

def bridgeTargetRoot {m : Nat} (base : D5Odd.ARoot5 m) (fiber : ARoot3 m) :
    RootState7 m :=
  ⟨bridgeTargetVec base fiber, bridgeTargetVec_root base fiber⟩

def bridgeFiberRoot {m : Nat} (w : RootState7 m) : ARoot3 m :=
  vec3OfPrefix (w.1 0 + w.1 1 + w.1 2 + w.1 3 + w.1 4) (w.1 5)

set_option linter.flexible false in
theorem baseRoot_bridgeTargetRoot {m : Nat}
    (base : D5Odd.ARoot5 m) (fiber : ARoot3 m) :
    baseRoot (bridgeTargetRoot base fiber) = base := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [baseRoot, bridgeTargetRoot, bridgeTargetVec, vec5OfPrefix]
  · rw [root5_sink_eq]
    ring

set_option linter.flexible false in
theorem bridgeFiberRoot_bridgeTargetRoot {m : Nat}
    (base : D5Odd.ARoot5 m) (fiber : ARoot3 m) :
    bridgeFiberRoot (bridgeTargetRoot base fiber) = fiber := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [bridgeFiberRoot, bridgeTargetRoot, bridgeTargetVec, vec3OfPrefix]
  rw [root3_sink_eq]
  ring

set_option linter.flexible false in
theorem bridgeTargetRoot_base_fiber {m : Nat} (w : RootState7 m) :
    bridgeTargetRoot (baseRoot w) (bridgeFiberRoot w) = w := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [bridgeTargetRoot, bridgeTargetVec, baseRoot,
    bridgeFiberRoot, vec5OfPrefix, vec3OfPrefix]
  rw [root7_sink_eq]
  ring

def bridgeRootEquiv (m : Nat) :
    D5Odd.ARoot5 m × ARoot3 m ≃ RootState7 m where
  toFun bf := bridgeTargetRoot bf.1 bf.2
  invFun w := (baseRoot w, bridgeFiberRoot w)
  left_inv := by
    intro bf
    rcases bf with ⟨base, fiber⟩
    simp [baseRoot_bridgeTargetRoot, bridgeFiberRoot_bridgeTargetRoot]
  right_inv := bridgeTargetRoot_base_fiber

def bridgeFiberDirectionOfSlot (i : Direction) : Direction3 :=
  match i.val with
  | 5 => 1
  | 6 => 2
  | _ => 0

def bridgeProductStep {m : Nat} (i : Direction) :
    ProductRoot m → ProductRoot m :=
  fun bf =>
    (baseAddQ (baseDirectionOfSlot i) bf.1,
      fiberAddQ (bridgeFiberDirectionOfSlot i) bf.2)

set_option linter.flexible false in
theorem bridgeFiberRoot_addQRoot {m : Nat}
    (i : Direction) (w : RootState7 m) :
    bridgeFiberRoot (addQRoot m i w) =
      fiberAddQ (bridgeFiberDirectionOfSlot i) (bridgeFiberRoot w) := by
  apply Subtype.ext
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [bridgeFiberRoot, addQRoot, addQ, q7, e7, vec3OfPrefix,
      fiberAddQ, bridgeFiberDirectionOfSlot]
  all_goals ring

theorem bridgeRootEquiv_symm_addQRoot {m : Nat}
    (i : Direction) (w : RootState7 m) :
    (bridgeRootEquiv m).symm (addQRoot m i w) =
      (baseAddQ (baseDirectionOfSlot i) (baseRoot w),
        fiberAddQ (bridgeFiberDirectionOfSlot i) (bridgeFiberRoot w)) := by
  ext <;>
    simp [bridgeRootEquiv, baseRoot_addQRoot, bridgeFiberRoot_addQRoot]

theorem bridgeRootEquiv_symm_addQRoot_bridgeRootEquiv {m : Nat}
    (i : Direction) (bf : ProductRoot m) :
    (bridgeRootEquiv m).symm
        (addQRoot m i ((bridgeRootEquiv m) bf)) =
      bridgeProductStep i bf := by
  rcases bf with ⟨base, fiber⟩
  rw [bridgeRootEquiv_symm_addQRoot]
  simp [bridgeProductStep, bridgeRootEquiv, baseRoot_bridgeTargetRoot,
    bridgeFiberRoot_bridgeTargetRoot]

end Additive4Plus2
end Handoff
end D7Odd
