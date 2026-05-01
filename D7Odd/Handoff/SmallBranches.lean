import D7Odd.Handoff.Main
import D7Odd.Handoff.SmallRank3Certificates
import D7Odd.Handoff.SmallRank5Certificates

set_option linter.style.nativeDecide false

namespace D7Odd
namespace Handoff

def zmodToFin (m : Nat) [NeZero m] (t : ZMod m) : Fin m :=
  ⟨t.val, ZMod.val_lt t⟩

@[simp] theorem zmodToFin_natCast_of_lt {m n : Nat} [NeZero m] (h : n < m) :
    zmodToFin m (n : ZMod m) = ⟨n, h⟩ := by
  apply Fin.ext
  simp [zmodToFin, ZMod.val_natCast_of_lt h]

@[simp] theorem zmodToFin3_zero : zmodToFin 3 (0 : ZMod 3) = 0 := by native_decide
@[simp] theorem zmodToFin3_one : zmodToFin 3 (1 : ZMod 3) = 1 := by native_decide
@[simp] theorem zmodToFin3_two : zmodToFin 3 (2 : ZMod 3) = 2 := by native_decide

@[simp] theorem zmodToFin5_zero : zmodToFin 5 (0 : ZMod 5) = 0 := by native_decide
@[simp] theorem zmodToFin5_one : zmodToFin 5 (1 : ZMod 5) = 1 := by native_decide
@[simp] theorem zmodToFin5_two : zmodToFin 5 (2 : ZMod 5) = 2 := by native_decide
@[simp] theorem zmodToFin5_three : zmodToFin 5 (3 : ZMod 5) = 3 := by native_decide
@[simp] theorem zmodToFin5_four : zmodToFin 5 (4 : ZMod 5) = 4 := by native_decide

def smallSchedule3 : RootFlatSchedule 3 where
  dir := fun t w c => smallDir3 (zmodToFin 3 t) w c

def smallSchedule5 : RootFlatSchedule 5 where
  dir := fun t w c => smallDir5 (zmodToFin 5 t) w c

theorem smallSchedule3_rowLatin : smallSchedule3.rowLatin := by
  intro t w
  exact smallDir3_latin (zmodToFin 3 t) w

theorem smallSchedule5_rowLatin : smallSchedule5.rowLatin := by
  intro t w
  exact smallDir5_latin (zmodToFin 5 t) w

theorem smallSchedule3_layerMap (t : ZMod 3) (c : Fin 7) :
    smallSchedule3.layerMap t c = smallLayer3 (zmodToFin 3 t) c := by
  rfl

theorem smallSchedule5_layerMap (t : ZMod 5) (c : Fin 7) :
    smallSchedule5.layerMap t c = smallLayer5 (zmodToFin 5 t) c := by
  rfl

theorem smallSchedule3_layerBijective : smallSchedule3.layerBijective := by
  intro t c
  rw [smallSchedule3_layerMap]
  exact smallLayer3_bijective (zmodToFin 3 t) c

theorem smallSchedule5_layerBijective : smallSchedule5.layerBijective := by
  intro t c
  rw [smallSchedule5_layerMap]
  exact smallLayer5_bijective (zmodToFin 5 t) c

theorem smallSchedule3_returnMap (c : Fin 7) :
    smallSchedule3.returnMap c = smallReturn3 c := by
  funext w
  unfold RootFlatSchedule.returnMap
  rw [show List.range 3 = [0, 1, 2] by native_decide]
  simp [RootFlatSchedule.layerMap, smallSchedule3, smallReturn3, smallLayer3]

theorem smallSchedule5_returnMap (c : Fin 7) :
    smallSchedule5.returnMap c = smallReturn5 c := by
  funext w
  unfold RootFlatSchedule.returnMap
  rw [show List.range 5 = [0, 1, 2, 3, 4] by native_decide]
  simp [RootFlatSchedule.layerMap, smallSchedule5, smallReturn5, smallLayer5]

theorem smallSchedule3_returnsSingleCycle : smallSchedule3.returnsSingleCycle := by
  intro c
  rw [smallSchedule3_returnMap]
  exact smallReturn3_single_cycle c

theorem smallSchedule5_returnsSingleCycle : smallSchedule5.returnsSingleCycle := by
  intro c
  rw [smallSchedule5_returnMap]
  exact smallReturn5CycleTarget c

def smallRootFlatCertificate3 : RootFlatCertificate 3 where
  schedule := smallSchedule3
  rowLatin := smallSchedule3_rowLatin
  layerBijective := smallSchedule3_layerBijective
  returnsSingleCycle := smallSchedule3_returnsSingleCycle

def smallRootFlatCertificate5 : RootFlatCertificate 5 where
  schedule := smallSchedule5
  rowLatin := smallSchedule5_rowLatin
  layerBijective := smallSchedule5_layerBijective
  returnsSingleCycle := smallSchedule5_returnsSingleCycle

theorem smallHamilton3 : HamiltonDecompositionD7 3 :=
  certificate_implies_hamilton smallRootFlatCertificate3

theorem smallHamilton5 : HamiltonDecompositionD7 5 :=
  certificate_implies_hamilton smallRootFlatCertificate5

def smallBranchResults : SmallBranchResults where
  m3 := smallHamilton3
  m5 := smallHamilton5

end Handoff
end D7Odd
