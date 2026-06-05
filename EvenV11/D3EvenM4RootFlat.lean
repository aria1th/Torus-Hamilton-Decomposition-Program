import EvenV11.D3EvenM4
import EvenV11.D3EvenRouteERootFlatBridge

set_option linter.style.nativeDecide false

namespace EvenV11
namespace D3EvenM4RootFlat

abbrev RootState4 := D3EvenRouteEGeSix.RootState 4

def layerRootEquiv4 :
    D3EvenM4.Vertex4 ≃ ZMod 4 × RootState4 :=
  D3EvenRouteEGeSix.layerRootEquiv 4

def schedule :
    Shared.RootFlatSchedule (Shared.TorusColor 3)
      (Shared.TorusDirection 3) RootState4 4 where
  dir := fun t w c =>
    D3EvenM4.colorDir c (layerRootEquiv4.symm (t, w))
  step := D3EvenRouteERootFlatBridge.rootStep 4

theorem schedule_layerMap_eq
    (t : ZMod 4) (c : Shared.TorusColor 3) (w : RootState4) :
    schedule.layerMap t c w =
      ((layerRootEquiv4)
        (Shared.cayleyColorStep D3EvenM4.colorDir c
          (layerRootEquiv4.symm (t, w)))).2 := by
  simp only [Shared.RootFlatSchedule.layerMap, schedule]
  generalize hdir :
    D3EvenM4.colorDir c (layerRootEquiv4.symm (t, w)) = i
  have hdir' :
      D3EvenM4.colorDir c
        (fun j : Fin 3 =>
          if j = (0 : Fin 3) then w.1
          else if j = (1 : Fin 3) then w.2
          else t - w.1 - w.2) = i := by
    simpa [layerRootEquiv4, D3EvenRouteEGeSix.layerRootEquiv] using hdir
  fin_cases i <;>
    simp [D3EvenRouteERootFlatBridge.rootStep, Shared.cayleyColorStep,
      Shared.torusBasis, layerRootEquiv4, D3EvenRouteEGeSix.layerRootEquiv,
      hdir']

theorem schedule_edgePartition :
    schedule.edgePartition := by
  intro t w i
  simpa [Shared.RootFlatSchedule.edgePartition, schedule] using
    D3EvenM4.edgePartition (layerRootEquiv4.symm (t, w)) i

theorem schedule_rowLatin :
    schedule.rowLatin :=
  Shared.RootFlatSchedule.rowLatin_of_edgePartition schedule_edgePartition

theorem schedule_layerBijective :
    schedule.layerBijective := by
  intro t c
  fin_cases c <;> native_decide +revert

def rootOfVertex (x : D3EvenM4.Vertex4) : RootState4 :=
  (layerRootEquiv4 x).2

def fourthIndex (i : Fin 16) : Fin 64 :=
  ⟨4 * i.val, by omega⟩

def cycle0Root (i : Fin 16) : RootState4 :=
  rootOfVertex (D3EvenM4.cycle0 (fourthIndex i))

def cycle1Root (i : Fin 16) : RootState4 :=
  rootOfVertex (D3EvenM4.cycle1 (fourthIndex i))

def cycle2Root (i : Fin 16) : RootState4 :=
  rootOfVertex (D3EvenM4.cycle2 (fourthIndex i))

def rank0RootFin (w : RootState4) : Fin 16 :=
  ⟨(D3EvenM4.rank0Fin (layerRootEquiv4.symm (0, w))).val / 4, by
    have hlt := (D3EvenM4.rank0Fin (layerRootEquiv4.symm (0, w))).isLt
    omega⟩

def rank1RootFin (w : RootState4) : Fin 16 :=
  ⟨(D3EvenM4.rank1Fin (layerRootEquiv4.symm (0, w))).val / 4, by
    have hlt := (D3EvenM4.rank1Fin (layerRootEquiv4.symm (0, w))).isLt
    omega⟩

def rank2RootFin (w : RootState4) : Fin 16 :=
  ⟨(D3EvenM4.rank2Fin (layerRootEquiv4.symm (0, w))).val / 4, by
    have hlt := (D3EvenM4.rank2Fin (layerRootEquiv4.symm (0, w))).isLt
    omega⟩

def cycle0RootEquiv : Fin 16 ≃ RootState4 where
  toFun := cycle0Root
  invFun := rank0RootFin
  left_inv := by
    intro i
    native_decide +revert
  right_inv := by
    intro w
    native_decide +revert

def cycle1RootEquiv : Fin 16 ≃ RootState4 where
  toFun := cycle1Root
  invFun := rank1RootFin
  left_inv := by
    intro i
    native_decide +revert
  right_inv := by
    intro w
    native_decide +revert

def cycle2RootEquiv : Fin 16 ≃ RootState4 where
  toFun := cycle2Root
  invFun := rank2RootFin
  left_inv := by
    intro i
    native_decide +revert
  right_inv := by
    intro w
    native_decide +revert

theorem cycle0Root_step :
    ∀ i : Fin 16,
      cycle0Root (i + 1) = schedule.returnMap 0 (cycle0Root i) := by
  native_decide

theorem cycle1Root_step :
    ∀ i : Fin 16,
      cycle1Root (i + 1) = schedule.returnMap 1 (cycle1Root i) := by
  native_decide

theorem cycle2Root_step :
    ∀ i : Fin 16,
      cycle2Root (i + 1) = schedule.returnMap 2 (cycle2Root i) := by
  native_decide

theorem schedule_returnsSingleCycle :
    schedule.returnsSingleCycle := by
  intro c
  fin_cases c
  · exact (Shared.CycleCoordinate.ofFinEquiv
      cycle0RootEquiv cycle0Root_step).singleCycle
  · exact (Shared.CycleCoordinate.ofFinEquiv
      cycle1RootEquiv cycle1Root_step).singleCycle
  · exact (Shared.CycleCoordinate.ofFinEquiv
      cycle2RootEquiv cycle2Root_step).singleCycle

theorem schedule_stepConjugacy :
    ∀ c : Shared.TorusColor 3, ∀ tw : ZMod 4 × RootState4,
      Shared.cayleyColorStep
        (finalD3RootFlatModelColorDir schedule layerRootEquiv4.symm)
        c (layerRootEquiv4.symm tw) =
      layerRootEquiv4.symm (schedule.fullStep c tw) := by
  intro c tw
  apply layerRootEquiv4.injective
  calc
    layerRootEquiv4
        (Shared.cayleyColorStep
          (finalD3RootFlatModelColorDir schedule layerRootEquiv4.symm)
          c (layerRootEquiv4.symm tw))
        =
        layerRootEquiv4
          (Shared.cayleyColorStep D3EvenM4.colorDir c
            (layerRootEquiv4.symm tw)) := by
          unfold finalD3RootFlatModelColorDir
          unfold finalRootFlatModelColorDir
          simp [schedule]
    _ = schedule.fullStep c tw := by
          rcases tw with ⟨t, w⟩
          apply Prod.ext
          · change
              D3EvenRouteEGeSix.sumLayer 4
                  (Shared.cayleyColorStep D3EvenM4.colorDir c
                    (layerRootEquiv4.symm (t, w))) =
                t + 1
            rw [Shared.cayleyColorStep]
            rw [D3EvenRouteEGeSix.sumLayer_add_torusBasis]
            simp [layerRootEquiv4]
          · simp [Shared.RootFlatSchedule.fullStep, schedule_layerMap_eq]
    _ = layerRootEquiv4 (layerRootEquiv4.symm (schedule.fullStep c tw)) := by
          simp

theorem rootFlatModel :
    FinalD3EvenRootFlatModel 4 RootState4 schedule layerRootEquiv4.symm :=
  finalRootFlatTorusModel_of_fields
    schedule_rowLatin
    schedule_layerBijective
    schedule_returnsSingleCycle
    schedule_stepConjugacy

theorem rootFlatCertificate :
    FinalD3EvenRootFlatCertificate 4 :=
  finalRootFlatTorusCertificate_of_model rootFlatModel

theorem rootFlatCertificateFamily_of_routeE_zero_layer_rankPackage
    (hZero :
      ∀ {m : Nat} [NeZero m], Even m → 6 ≤ m →
        ∀ c : Shared.TorusColor 3,
          Function.Bijective
            (D3EvenRouteEGeSix.routeELayerMap m (0 : ZMod m) c))
    (hRank :
      ∀ {m : Nat} [NeZero m], Even m → 6 ≤ m →
        D3EvenRouteEGeSix.RouteEReturnModelRankPackage m) :
    FinalD3EvenRootFlatCertificateFamily :=
  D3EvenRouteERootFlatBridge.rootFlatCertificateFamily_of_m4_zero_layer_rankPackage
    rootFlatCertificate hZero hRank

theorem rootFlatCertificateFamily_of_routeE_zero_layer_returnModels
    (hZero :
      ∀ {m : Nat} [NeZero m], Even m → 6 ≤ m →
        ∀ c : Shared.TorusColor 3,
          Function.Bijective
            (D3EvenRouteEGeSix.routeELayerMap m (0 : ZMod m) c))
    (hReturnZero :
      ∀ {m : Nat} [NeZero m], Even m → 6 ≤ m →
        Shared.IsSingleCycleMap (D3EvenRouteEGeSix.routeEReturnZeroModel m))
    (hReturnOne :
      ∀ {m : Nat} [NeZero m], Even m → 6 ≤ m →
        Shared.IsSingleCycleMap (D3EvenRouteEGeSix.routeEReturnOneModel m))
    (hReturnTwo :
      ∀ {m : Nat} [NeZero m], Even m → 6 ≤ m →
        Shared.IsSingleCycleMap (D3EvenRouteEGeSix.routeEReturnTwoModel m)) :
    FinalD3EvenRootFlatCertificateFamily :=
  D3EvenRouteERootFlatBridge.rootFlatCertificateFamily_of_m4_zero_layer_returnModels
    rootFlatCertificate hZero hReturnZero hReturnOne hReturnTwo

theorem rootFlatCertificateFamily_of_routeE_residue_rankPackages
    (hZeroOrTwo :
      ∀ {m : Nat} [NeZero m], Even m → 6 ≤ m →
        (m % 6 = 0 ∨ m % 6 = 2) →
          ∀ c : Shared.TorusColor 3,
            Function.Bijective
              (D3EvenRouteEGeSix.routeELayerMap m (0 : ZMod m) c))
    (hZeroFour :
      ∀ {m : Nat} [NeZero m], Even m → 6 ≤ m →
        m % 6 = 4 →
          ∀ c : Shared.TorusColor 3,
            Function.Bijective
              (D3EvenRouteEGeSix.routeELayerMap m (0 : ZMod m) c))
    (hRankOrTwo :
      ∀ {m : Nat} [NeZero m], Even m → 6 ≤ m →
        (m % 6 = 0 ∨ m % 6 = 2) →
          D3EvenRouteEGeSix.RouteEReturnModelRankPackage m)
    (hRankFour :
      ∀ {m : Nat} [NeZero m], Even m → 6 ≤ m →
        m % 6 = 4 →
          D3EvenRouteEGeSix.RouteEReturnModelRankPackage m) :
    FinalD3EvenRootFlatCertificateFamily := by
  apply rootFlatCertificateFamily_of_routeE_zero_layer_rankPackage
  · intro m _ hm_even hm6
    exact D3EvenRouteEGeSix.routeELayerMap_zero_layer_bijective_of_even_mod_cases
      hm_even (hZeroOrTwo hm_even hm6) (hZeroFour hm_even hm6)
  · intro m _ hm_even hm6
    exact D3EvenRouteEGeSix.routeEReturnModelRankPackageOfEvenModCases
      hm_even (hRankOrTwo hm_even hm6) (hRankFour hm_even hm6)

theorem rootFlatCertificateFamily_of_routeE_tail_rankPackages
    (hZeroTail :
      ∀ {m : Nat} [NeZero m], Even m → 14 ≤ m →
        ∀ c : Shared.TorusColor 3,
          Function.Bijective
            (D3EvenRouteEGeSix.routeELayerMap m (0 : ZMod m) c))
    (hRankTail :
      ∀ {m : Nat} [NeZero m], Even m → 14 ≤ m →
        D3EvenRouteEGeSix.RouteEReturnModelRankPackage m) :
    FinalD3EvenRootFlatCertificateFamily := by
  apply rootFlatCertificateFamily_of_routeE_zero_layer_rankPackage
  · intro m _ hm_even hm6
    exact D3EvenRouteEGeSix.routeELayerMap_zero_layer_bijective_of_even_ge_six_tail
      hm_even hm6 (hZeroTail hm_even)
  · intro m _ hm_even hm6
    exact D3EvenRouteEGeSix.routeEReturnModelRankPackageOfEvenGeSixTail
      hm_even hm6 (hRankTail hm_even)

theorem rootFlatCertificateFamily_of_routeE_tail_returnModels
    (hZeroTail :
      ∀ {m : Nat} [NeZero m], Even m → 14 ≤ m →
        ∀ c : Shared.TorusColor 3,
          Function.Bijective
            (D3EvenRouteEGeSix.routeELayerMap m (0 : ZMod m) c))
    (hReturnZeroTail :
      ∀ {m : Nat} [NeZero m], Even m → 14 ≤ m →
        Shared.IsSingleCycleMap (D3EvenRouteEGeSix.routeEReturnZeroModel m))
    (hReturnOneTail :
      ∀ {m : Nat} [NeZero m], Even m → 14 ≤ m →
        Shared.IsSingleCycleMap (D3EvenRouteEGeSix.routeEReturnOneModel m))
    (hReturnTwoTail :
      ∀ {m : Nat} [NeZero m], Even m → 14 ≤ m →
        Shared.IsSingleCycleMap (D3EvenRouteEGeSix.routeEReturnTwoModel m)) :
    FinalD3EvenRootFlatCertificateFamily := by
  apply rootFlatCertificateFamily_of_routeE_zero_layer_returnModels
  · intro m _ hm_even hm6
    exact D3EvenRouteEGeSix.routeELayerMap_zero_layer_bijective_of_even_ge_six_tail
      hm_even hm6 (hZeroTail hm_even)
  · intro m _ hm_even hm6
    exact D3EvenRouteEGeSix.routeEReturnZeroModel_singleCycle_of_even_ge_six_tail
      hm_even hm6 (hReturnZeroTail hm_even)
  · intro m _ hm_even hm6
    exact D3EvenRouteEGeSix.routeEReturnOneModel_singleCycle_of_even_ge_six_tail
      hm_even hm6 (hReturnOneTail hm_even)
  · intro m _ hm_even hm6
    exact D3EvenRouteEGeSix.routeEReturnTwoModel_singleCycle_of_even_ge_six_tail
      hm_even hm6 (hReturnTwoTail hm_even)

theorem rootFlatCertificateFamily_of_routeE_tail_residue_rankPackages
    (hZeroOrTwoTail :
      ∀ {m : Nat} [NeZero m], Even m → 14 ≤ m →
        (m % 6 = 0 ∨ m % 6 = 2) →
          ∀ c : Shared.TorusColor 3,
            Function.Bijective
              (D3EvenRouteEGeSix.routeELayerMap m (0 : ZMod m) c))
    (hZeroFourTail :
      ∀ {m : Nat} [NeZero m], Even m → 14 ≤ m →
        m % 6 = 4 →
          ∀ c : Shared.TorusColor 3,
            Function.Bijective
              (D3EvenRouteEGeSix.routeELayerMap m (0 : ZMod m) c))
    (hRankOrTwoTail :
      ∀ {m : Nat} [NeZero m], Even m → 14 ≤ m →
        (m % 6 = 0 ∨ m % 6 = 2) →
          D3EvenRouteEGeSix.RouteEReturnModelRankPackage m)
    (hRankFourTail :
      ∀ {m : Nat} [NeZero m], Even m → 14 ≤ m →
        m % 6 = 4 →
          D3EvenRouteEGeSix.RouteEReturnModelRankPackage m) :
    FinalD3EvenRootFlatCertificateFamily := by
  apply rootFlatCertificateFamily_of_routeE_tail_rankPackages
  · intro m _ hm_even hm14
    exact D3EvenRouteEGeSix.routeELayerMap_zero_layer_bijective_of_even_mod_cases
      hm_even
      (hZeroOrTwoTail hm_even hm14)
      (hZeroFourTail hm_even hm14)
  · intro m _ hm_even hm14
    exact D3EvenRouteEGeSix.routeEReturnModelRankPackageOfEvenModCases
      hm_even
      (hRankOrTwoTail hm_even hm14)
      (hRankFourTail hm_even hm14)

end D3EvenM4RootFlat
end EvenV11
