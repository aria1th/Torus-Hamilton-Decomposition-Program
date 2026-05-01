import D7Odd.ReturnEngine
import D7Odd.Handoff.CanonicalFamily
import Shared.RootFlat

namespace D7Odd

abbrev Vertex7 (m : Nat) := Vec7 m

theorem sum7_sub (m : Nat) (x y : Vec7 m) :
    sum7 m (x - y) = sum7 m x - sum7 m y := by
  simp [sum7, Finset.sum_sub_distrib]

theorem sum7_smul (m : Nat) (a : ZMod m) (w : Vec7 m) :
    sum7 m (a • w) = a * sum7 m w := by
  simp [sum7, Finset.mul_sum]

def layerOf {m : Nat} (x : Vertex7 m) : ZMod m :=
  sum7 m x

def rootAtLayer {m : Nat} (x : Vertex7 m) : Handoff.RootState7 m :=
  ⟨x - layerOf x • e7 m 6, by
    unfold Root7 layerOf
    calc
      sum7 m (x - sum7 m x • e7 m 6)
          = sum7 m x - sum7 m (sum7 m x • e7 m 6) := by
            rw [sum7_sub]
      _ = sum7 m x - sum7 m x * sum7 m (e7 m 6) := by
            rw [sum7_smul]
      _ = sum7 m x - sum7 m x * 1 := by
            rw [sum7_e7]
      _ = 0 := by ring⟩

def torusOfLayerRoot {m : Nat} (t : ZMod m) (w : Handoff.RootState7 m) :
    Vertex7 m :=
  w.1 + t • e7 m 6

theorem layerOf_torusOfLayerRoot {m : Nat} (t : ZMod m)
    (w : Handoff.RootState7 m) :
    layerOf (torusOfLayerRoot t w) = t := by
  unfold layerOf torusOfLayerRoot
  calc
    sum7 m (w.1 + t • e7 m 6)
        = sum7 m w.1 + sum7 m (t • e7 m 6) := by
          rw [sum7_add]
    _ = 0 + t * sum7 m (e7 m 6) := by
          rw [w.2, sum7_smul]
    _ = t := by
          rw [sum7_e7]
          ring

theorem rootAtLayer_torusOfLayerRoot {m : Nat} (t : ZMod m)
    (w : Handoff.RootState7 m) :
    rootAtLayer (torusOfLayerRoot t w) = w := by
  apply Subtype.ext
  ext i
  change
    (torusOfLayerRoot t w -
        layerOf (torusOfLayerRoot t w) • e7 m 6) i = w.1 i
  rw [layerOf_torusOfLayerRoot t w]
  by_cases hi : i = 6
  · subst hi
    simp [torusOfLayerRoot, e7]
  · simp [torusOfLayerRoot, e7, hi]

theorem torusOfLayerRoot_layerOf_rootAtLayer {m : Nat} (x : Vertex7 m) :
    torusOfLayerRoot (layerOf x) (rootAtLayer x) = x := by
  ext i
  simp [torusOfLayerRoot, rootAtLayer]

def layerRootEquiv {m : Nat} : (ZMod m × Handoff.RootState7 m) ≃ Vertex7 m where
  toFun tw := torusOfLayerRoot tw.1 tw.2
  invFun x := (layerOf x, rootAtLayer x)
  left_inv := by
    rintro ⟨t, w⟩
    simp [layerOf_torusOfLayerRoot, rootAtLayer_torusOfLayerRoot]
  right_inv := torusOfLayerRoot_layerOf_rootAtLayer

theorem layerOf_sub_q7 {m : Nat} (x : Vertex7 m) (i : Direction) :
    layerOf (x - q7 m i) = layerOf x := by
  unfold layerOf
  calc
    sum7 m (x - q7 m i) = sum7 m x - sum7 m (q7 m i) := by
      rw [sum7_sub]
    _ = sum7 m x := by
      rw [Handoff.sum7_q7_zero]
      simp

theorem rootAtLayer_sub_q7 {m : Nat} (x : Vertex7 m) (i : Direction) :
    rootAtLayer (x - q7 m i) =
      Handoff.subQRoot m i (rootAtLayer x) := by
  apply Subtype.ext
  ext j
  simp [rootAtLayer, Handoff.subQRoot, Handoff.subQ, layerOf_sub_q7]
  abel

def selectorFamilyOfRootFlat {m : Nat} (S : Handoff.RootFlatSchedule m) :
    SelectorFamily m where
  dir := fun c x => S.dir (layerOf x) (rootAtLayer x) c

def rootFlatLayerStep {m : Nat} (S : Handoff.RootFlatSchedule m) (c : Color) :
    ZMod m × Handoff.RootState7 m → ZMod m × Handoff.RootState7 m :=
  fun tw => (tw.1 + 1, S.layerMap tw.1 c tw.2)

theorem rootFlatLayerStep_single_cycle {m : Nat} [NeZero m]
    {S : Handoff.RootFlatSchedule m}
    (hLayer : S.layerBijective) (hReturn : S.returnsSingleCycle)
    (c : Color) :
    Handoff.IsSingleCycleMap (rootFlatLayerStep S c) := by
  have hSharedLayer : S.toShared.layerBijective :=
    (Handoff.RootFlatSchedule.toShared_layerBijective S).2 hLayer
  have hSharedReturn : S.toShared.returnsSingleCycle :=
    (Handoff.RootFlatSchedule.toShared_returnsSingleCycle S).2 hReturn
  have hCycle : Shared.IsSingleCycleMap (S.toShared.fullStep c) :=
    Shared.RootFlatSchedule.fullStep_singleCycle_of_return
      S.toShared hSharedLayer (hSharedReturn c)
  simpa [Shared.IsSingleCycleMap, Handoff.IsSingleCycleMap,
    Handoff.RootFlatSchedule.toShared, Shared.RootFlatSchedule.fullStep,
    Shared.RootFlatSchedule.layerMap, rootFlatLayerStep] using hCycle

theorem torusOfLayerRoot_add_direction {m : Nat} (t : ZMod m)
    (w : Handoff.RootState7 m) (i : Direction) :
    torusOfLayerRoot t w + e7 m i =
      torusOfLayerRoot (t + 1) (Handoff.addQRoot m i w) := by
  ext j
  simp [torusOfLayerRoot, Handoff.addQRoot, Handoff.addQ, q7]
  by_cases hj6 : j = 6
  · subst j
    by_cases hi6 : i = 6 <;> simp [e7, hi6] <;> ring
  · by_cases hji : j = i
    · have hi6 : i ≠ 6 := by
        intro hi
        exact hj6 (hji.trans hi)
      simp [e7, hji, hi6]
    · simp [e7, hj6, hji]

theorem colorStep_torusOfLayerRoot {m : Nat}
    (S : Handoff.RootFlatSchedule m) (c : Color)
    (t : ZMod m) (w : Handoff.RootState7 m) :
    colorStep (selectorFamilyOfRootFlat S) c (torusOfLayerRoot t w) =
      torusOfLayerRoot (t + 1) (S.layerMap t c w) := by
  have hlayer : layerOf (torusOfLayerRoot t w) = t :=
    layerOf_torusOfLayerRoot t w
  have hroot : rootAtLayer (torusOfLayerRoot t w) = w :=
    rootAtLayer_torusOfLayerRoot t w
  unfold colorStep selectorFamilyOfRootFlat
  change torusOfLayerRoot t w + e7 m
      (S.dir (layerOf (torusOfLayerRoot t w))
        (rootAtLayer (torusOfLayerRoot t w)) c) =
    torusOfLayerRoot (t + 1) (S.layerMap t c w)
  rw [hlayer, hroot]
  simp [Handoff.RootFlatSchedule.layerMap, torusOfLayerRoot_add_direction]

theorem colorStep_layerRootEquiv {m : Nat}
    (S : Handoff.RootFlatSchedule m) (c : Color)
    (tw : ZMod m × Handoff.RootState7 m) :
    colorStep (selectorFamilyOfRootFlat S) c (layerRootEquiv tw) =
      layerRootEquiv (rootFlatLayerStep S c tw) := by
  rcases tw with ⟨t, w⟩
  exact colorStep_torusOfLayerRoot S c t w

theorem selectorFamilyOfRootFlat_exactCover {m : Nat}
    {S : Handoff.RootFlatSchedule m} (hLayer : S.layerBijective) :
    IsExactCover (selectorFamilyOfRootFlat S) := by
  intro c y
  let t : ZMod m := layerOf y
  let r : Handoff.RootState7 m := rootAtLayer y
  rcases (hLayer t c).2 r with ⟨w, hw⟩
  let i : Direction := S.dir t w c
  have hw_sub : w = Handoff.subQRoot m i r := by
    have hleft :
        Handoff.subQRoot m i (S.layerMap t c w) = w := by
      simp [Handoff.RootFlatSchedule.layerMap, i, Handoff.subQRoot_addQRoot]
    exact hleft.symm.trans (congrArg (Handoff.subQRoot m i) hw)
  refine ⟨i, ?_, ?_⟩
  · have hlayer : layerOf (y - q7 m i) = t := by
      simpa [t] using layerOf_sub_q7 y i
    have hroot :
        rootAtLayer (y - q7 m i) = Handoff.subQRoot m i r := by
      simpa [r] using rootAtLayer_sub_q7 y i
    simp [selectorFamilyOfRootFlat, hlayer, hroot, hw_sub.symm, i]
  · intro j hj
    have hlayer : layerOf (y - q7 m j) = t := by
      simpa [t] using layerOf_sub_q7 y j
    have hroot :
        rootAtLayer (y - q7 m j) = Handoff.subQRoot m j r := by
      simpa [r] using rootAtLayer_sub_q7 y j
    have hdir :
        S.dir t (Handoff.subQRoot m j r) c = j := by
      simpa [selectorFamilyOfRootFlat, hlayer, hroot] using hj
    have hmap :
        S.layerMap t c (Handoff.subQRoot m j r) = r := by
      simp [Handoff.RootFlatSchedule.layerMap, hdir, Handoff.addQRoot_subQRoot]
    have hroot_eq : Handoff.subQRoot m j r = w :=
      (hLayer t c).1 (hmap.trans hw.symm)
    calc
      j = S.dir t (Handoff.subQRoot m j r) c := hdir.symm
      _ = S.dir t w c := by rw [hroot_eq]
      _ = i := rfl

theorem selectorFamilyOfRootFlat_latin {m : Nat}
    {S : Handoff.RootFlatSchedule m} (hRow : S.rowLatin) :
    IsLatin (selectorFamilyOfRootFlat S) := by
  intro x
  simpa [selectorFamilyOfRootFlat] using hRow (layerOf x) (rootAtLayer x)

theorem selectorFamilyOfRootFlat_colorStep_single_cycle {m : Nat} [NeZero m]
    {S : Handoff.RootFlatSchedule m}
    (hLayer : S.layerBijective) (hReturn : S.returnsSingleCycle)
    (c : Color) :
    IsSingleCycleMap (colorStep (selectorFamilyOfRootFlat S) c) := by
  have h :
      Handoff.IsSingleCycleMap
        (colorStep (selectorFamilyOfRootFlat S) c) := by
    exact Handoff.single_cycle_of_bijective_semiconj
      (f := rootFlatLayerStep S c)
      (g := colorStep (selectorFamilyOfRootFlat S) c)
      (φ := layerRootEquiv)
      (layerRootEquiv.bijective)
      (fun tw => (colorStep_layerRootEquiv S c tw).symm)
      (rootFlatLayerStep_single_cycle hLayer hReturn c)
  simpa [IsSingleCycleMap, Handoff.IsSingleCycleMap] using h

theorem selectorFamilyOfRootFlat_hamiltonian {m : Nat} [NeZero m]
    {S : Handoff.RootFlatSchedule m}
    (hLayer : S.layerBijective) (hReturn : S.returnsSingleCycle) :
    AllColorHamiltonian (selectorFamilyOfRootFlat S) := by
  intro c
  exact selectorFamilyOfRootFlat_colorStep_single_cycle hLayer hReturn c

def TorusHamiltonDecompositionD7 (m : Nat) : Prop :=
  ∃ F : SelectorFamily m, IsExactCover F ∧ IsLatin F ∧
    ∀ c : Color, IsSingleCycleMap (colorStep F c)

theorem torusHamiltonDecompositionD7_of_hamiltonDecomposition {m : Nat}
    (h : HamiltonDecompositionD7 m) :
    TorusHamiltonDecompositionD7 m := by
  exact h

theorem rootFlatCertificate_to_hamiltonDecomposition {m : Nat} [NeZero m]
    (cert : Handoff.RootFlatCertificate m) :
    HamiltonDecompositionD7 m := by
  refine ⟨selectorFamilyOfRootFlat cert.schedule, ?_, ?_, ?_⟩
  · exact selectorFamilyOfRootFlat_exactCover cert.layerBijective
  · exact selectorFamilyOfRootFlat_latin cert.rowLatin
  · exact selectorFamilyOfRootFlat_hamiltonian cert.layerBijective cert.returnsSingleCycle

theorem hamiltonDecompositionD7_of_handoff {m : Nat} [NeZero m]
    (h : Handoff.HamiltonDecompositionD7 m) :
    HamiltonDecompositionD7 m := by
  rcases h with ⟨cert⟩
  exact rootFlatCertificate_to_hamiltonDecomposition cert

theorem torusHamiltonDecompositionD7_of_handoff {m : Nat} [NeZero m]
    (h : Handoff.HamiltonDecompositionD7 m) :
    TorusHamiltonDecompositionD7 m :=
  torusHamiltonDecompositionD7_of_hamiltonDecomposition
    (hamiltonDecompositionD7_of_handoff h)

theorem D7_odd_torus_unconditional {m : Nat} [NeZero m]
    (hodd : Odd m) (hm3 : 3 <= m) :
    TorusHamiltonDecompositionD7 m := by
  exact torusHamiltonDecompositionD7_of_handoff (Handoff.main_odd hm3 hodd)

end D7Odd
