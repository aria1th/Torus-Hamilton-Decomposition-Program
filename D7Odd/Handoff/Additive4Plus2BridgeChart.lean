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

structure BridgeProductRootSchedule (m : Nat) where
  dir : ZMod m → ProductRoot m → Color → Direction

namespace BridgeProductRootSchedule

def rowLatin {m : Nat} (P : BridgeProductRootSchedule m) : Prop :=
  ∀ t bf, Function.Bijective fun c : Color => P.dir t bf c

def layerMap {m : Nat} (P : BridgeProductRootSchedule m)
    (t : ZMod m) (c : Color) : ProductRoot m → ProductRoot m :=
  fun bf => bridgeProductStep (P.dir t bf c) bf

def layerBijective {m : Nat} (P : BridgeProductRootSchedule m) : Prop :=
  ∀ t c, Function.Bijective (P.layerMap t c)

def returnMap {m : Nat} [NeZero m]
    (P : BridgeProductRootSchedule m) (c : Color) :
    ProductRoot m → ProductRoot m :=
  fun bf => ((List.range m).foldl
    (fun x (t : Nat) => P.layerMap (t : ZMod m) c x) bf)

def returnsSingleCycle {m : Nat} [NeZero m]
    (P : BridgeProductRootSchedule m) : Prop :=
  ∀ c : Color, IsSingleCycleMap (P.returnMap c)

def toRootFlatSchedule {m : Nat} (P : BridgeProductRootSchedule m) :
    RootFlatSchedule m where
  dir := fun t w c => P.dir t ((bridgeRootEquiv m).symm w) c

theorem toRootFlatSchedule_rowLatin {m : Nat}
    (P : BridgeProductRootSchedule m) :
    P.toRootFlatSchedule.rowLatin ↔ P.rowLatin := by
  constructor
  · intro h t bf
    simpa [toRootFlatSchedule] using h t ((bridgeRootEquiv m) bf)
  · intro h t w
    exact h t ((bridgeRootEquiv m).symm w)

theorem toRootFlatSchedule_layerMap_conj {m : Nat}
    (P : BridgeProductRootSchedule m) (t : ZMod m) (c : Color)
    (bf : ProductRoot m) :
    (bridgeRootEquiv m).symm
        (P.toRootFlatSchedule.layerMap t c ((bridgeRootEquiv m) bf)) =
      P.layerMap t c bf := by
  simp [toRootFlatSchedule, RootFlatSchedule.layerMap, layerMap,
    bridgeRootEquiv_symm_addQRoot_bridgeRootEquiv]

theorem toRootFlatSchedule_layerBijective {m : Nat}
    (P : BridgeProductRootSchedule m) (h : P.layerBijective) :
    P.toRootFlatSchedule.layerBijective := by
  intro t c
  exact Shared.bijective_of_equiv_conj
    (e := bridgeRootEquiv m) (f := P.toRootFlatSchedule.layerMap t c)
    (g := P.layerMap t c) (h t c)
    (P.toRootFlatSchedule_layerMap_conj t c)

theorem toRootFlatSchedule_returnMap_conj
    {m : Nat} [NeZero m] (P : BridgeProductRootSchedule m)
    (c : Color) (bf : ProductRoot m) :
    (bridgeRootEquiv m).symm
        (P.toRootFlatSchedule.returnMap c ((bridgeRootEquiv m) bf)) =
      P.returnMap c bf := by
  unfold RootFlatSchedule.returnMap returnMap
  let F : RootState7 m → Nat → RootState7 m :=
    fun w (t : Nat) => P.toRootFlatSchedule.layerMap (t : ZMod m) c w
  let G : ProductRoot m → Nat → ProductRoot m :=
    fun bf (t : Nat) => P.layerMap (t : ZMod m) c bf
  have hfold :
      ∀ ts : List Nat, ∀ bf : ProductRoot m,
        (bridgeRootEquiv m).symm (ts.foldl F ((bridgeRootEquiv m) bf)) =
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
            F ((bridgeRootEquiv m) bf) t =
              (bridgeRootEquiv m) (G bf t) := by
          simp only [F, G]
          apply (bridgeRootEquiv m).symm.injective
          simpa using P.toRootFlatSchedule_layerMap_conj (t : ZMod m) c bf
        rw [hstep]
        exact ih (G bf t)
  simpa [F, G] using hfold (List.range m) bf

theorem toRootFlatSchedule_returnsSingleCycle
    {m : Nat} [NeZero m] (P : BridgeProductRootSchedule m)
    (h : P.returnsSingleCycle) :
    P.toRootFlatSchedule.returnsSingleCycle := by
  intro c
  have hShared : Shared.IsSingleCycleMap (P.returnMap c) := by
    simpa [Shared.IsSingleCycleMap, IsSingleCycleMap] using h c
  have hCycle :=
    Shared.single_cycle_of_equiv_conj
      (e := bridgeRootEquiv m)
      (f := P.toRootFlatSchedule.returnMap c)
      (g := P.returnMap c)
      hShared
      (P.toRootFlatSchedule_returnMap_conj c)
  simpa [Shared.IsSingleCycleMap, IsSingleCycleMap] using hCycle

end BridgeProductRootSchedule

structure BridgeProductRootCertificate (m : Nat) [NeZero m] where
  schedule : BridgeProductRootSchedule m
  rowLatin : schedule.rowLatin
  layerBijective : schedule.layerBijective
  returnsSingleCycle : schedule.returnsSingleCycle

def BridgeProductRootCertificate.toRootFlatCertificate
    {m : Nat} [NeZero m] (cert : BridgeProductRootCertificate m) :
    RootFlatCertificate m where
  schedule := cert.schedule.toRootFlatSchedule
  rowLatin := (BridgeProductRootSchedule.toRootFlatSchedule_rowLatin
    cert.schedule).2 cert.rowLatin
  layerBijective :=
    BridgeProductRootSchedule.toRootFlatSchedule_layerBijective cert.schedule
      cert.layerBijective
  returnsSingleCycle :=
    BridgeProductRootSchedule.toRootFlatSchedule_returnsSingleCycle
      cert.schedule cert.returnsSingleCycle

theorem BridgeProductRootCertificate.toHamiltonDecompositionD7
    {m : Nat} [NeZero m] (cert : BridgeProductRootCertificate m) :
    HamiltonDecompositionD7 m :=
  certificate_implies_hamilton cert.toRootFlatCertificate

theorem BridgeProductRootCertificate.toSharedLayeredHamilton
    {m : Nat} [NeZero m] (cert : BridgeProductRootCertificate m) :
    Shared.RootFlatLayeredHamiltonDecomposition
      Color Direction (RootState7 m) m :=
  cert.toRootFlatCertificate.toSharedLayeredHamilton

end Additive4Plus2
end Handoff
end D7Odd
