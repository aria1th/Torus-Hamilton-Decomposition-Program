import EvenV11.FinalTargetD3RootFlatCertificateBridge
import EvenV11.D3EvenRouteEGeSix

namespace EvenV11
namespace D3EvenRouteERootFlatBridge

open D3EvenRouteEGeSix

def rootStep (m : Nat) (i : Shared.TorusDirection 3)
    (w : D3EvenRouteEGeSix.RootState m) :
    D3EvenRouteEGeSix.RootState m :=
  match i with
  | ⟨0, _⟩ => (w.1 + 1, w.2)
  | ⟨1, _⟩ => (w.1, w.2 + 1)
  | ⟨2, _⟩ => w
  | ⟨n + 3, h⟩ => by omega

def schedule (m : Nat) :
    Shared.RootFlatSchedule (Shared.TorusColor 3)
      (Shared.TorusDirection 3) (D3EvenRouteEGeSix.RootState m) m where
  dir := fun t w c =>
    D3EvenRouteEGeSix.colorDir m c
      ((D3EvenRouteEGeSix.layerRootEquiv m).symm (t, w))
  step := rootStep m

theorem schedule_layerMap_eq_routeELayerMap
    (m : Nat) (t : ZMod m) (c : Shared.TorusColor 3)
    (w : D3EvenRouteEGeSix.RootState m) :
    (schedule m).layerMap t c w =
      D3EvenRouteEGeSix.routeELayerMap m t c w := by
  simp only [Shared.RootFlatSchedule.layerMap, schedule,
    D3EvenRouteEGeSix.routeELayerMap]
  generalize hdir :
    D3EvenRouteEGeSix.colorDir m c
      ((D3EvenRouteEGeSix.layerRootEquiv m).symm (t, w)) = i
  have hdir' :
      D3EvenRouteEGeSix.colorDir m c
        (fun j : Fin 3 =>
          if j = (0 : Fin 3) then w.1
          else if j = (1 : Fin 3) then w.2
          else t - w.1 - w.2) = i := by
    simpa [D3EvenRouteEGeSix.layerRootEquiv] using hdir
  fin_cases i <;>
    simp [rootStep, Shared.cayleyColorStep, Shared.torusBasis,
      D3EvenRouteEGeSix.layerRootEquiv, hdir']

theorem schedule_prefixMap_eq_routeELayerPrefixMap
    (m : Nat) (c : Shared.TorusColor 3) :
    ∀ k : Nat, ∀ w : D3EvenRouteEGeSix.RootState m,
      (schedule m).prefixMap c k w =
        D3EvenRouteEGeSix.routeELayerPrefixMap m c k w
  | 0, w => by
      simp [Shared.RootFlatSchedule.prefixMap,
        D3EvenRouteEGeSix.routeELayerPrefixMap]
  | n + 1, w => by
      simp [Shared.RootFlatSchedule.prefixMap,
        D3EvenRouteEGeSix.routeELayerPrefixMap,
        schedule_layerMap_eq_routeELayerMap,
        schedule_prefixMap_eq_routeELayerPrefixMap m c n w]

theorem schedule_returnMap_eq_routeEReturnMap
    {m : Nat} [NeZero m] (c : Shared.TorusColor 3) :
    (schedule m).returnMap c =
      D3EvenRouteEGeSix.routeEReturnMap m c := by
  rw [Shared.RootFlatSchedule.returnMap_eq_prefixMap]
  funext w
  exact schedule_prefixMap_eq_routeELayerPrefixMap m c m w

theorem schedule_edgePartition (m : Nat) :
    (schedule m).edgePartition := by
  intro t w i
  simpa [Shared.RootFlatSchedule.edgePartition, schedule] using
    D3EvenRouteEGeSix.edgePartition m
      ((D3EvenRouteEGeSix.layerRootEquiv m).symm (t, w)) i

theorem schedule_rowLatin (m : Nat) :
    (schedule m).rowLatin :=
  Shared.RootFlatSchedule.rowLatin_of_edgePartition
    (schedule_edgePartition m)

theorem schedule_layerBijective_of_zero_layer
    {m : Nat} [NeZero m] (hm3 : 3 ≤ m)
    (hZero :
      ∀ c : Shared.TorusColor 3,
        Function.Bijective
          (D3EvenRouteEGeSix.routeELayerMap m (0 : ZMod m) c)) :
    (schedule m).layerBijective :=
  Shared.RootFlatSchedule.layerBijective_of_layerMap_apply_eq
    (fun t c => D3EvenRouteEGeSix.routeELayerMap m t c)
    (fun t c =>
      D3EvenRouteEGeSix.routeELayerMap_bijective_of_zero_layer
        hm3 hZero c t)
    (schedule_layerMap_eq_routeELayerMap m)

theorem schedule_returnsSingleCycle_of_routeEReturnMap
    {m : Nat} [NeZero m]
    (hReturn :
      ∀ c : Shared.TorusColor 3,
        Shared.IsSingleCycleMap (D3EvenRouteEGeSix.routeEReturnMap m c)) :
    (schedule m).returnsSingleCycle := by
  intro c
  rw [schedule_returnMap_eq_routeEReturnMap]
  exact hReturn c

theorem schedule_returnsSingleCycle_of_rankPackage
    {m : Nat} [NeZero m] (hm3 : 3 ≤ m)
    (pkg : D3EvenRouteEGeSix.RouteEReturnModelRankPackage m) :
    (schedule m).returnsSingleCycle :=
  schedule_returnsSingleCycle_of_routeEReturnMap
    (D3EvenRouteEGeSix.RouteEReturnModelRankPackage.returnMap_singleCycle
      pkg hm3)

theorem schedule_stepConjugacy
    {m : Nat} [NeZero m] :
    ∀ c : Shared.TorusColor 3,
    ∀ tw : ZMod m × D3EvenRouteEGeSix.RootState m,
      Shared.cayleyColorStep
        (finalD3RootFlatModelColorDir
          (schedule m) (D3EvenRouteEGeSix.layerRootEquiv m).symm)
        c ((D3EvenRouteEGeSix.layerRootEquiv m).symm tw) =
      (D3EvenRouteEGeSix.layerRootEquiv m).symm
        ((schedule m).fullStep c tw) := by
  intro c tw
  apply (D3EvenRouteEGeSix.layerRootEquiv m).injective
  calc
    (D3EvenRouteEGeSix.layerRootEquiv m)
        (Shared.cayleyColorStep
          (finalD3RootFlatModelColorDir
            (schedule m) (D3EvenRouteEGeSix.layerRootEquiv m).symm)
          c ((D3EvenRouteEGeSix.layerRootEquiv m).symm tw))
        =
        (D3EvenRouteEGeSix.layerRootEquiv m)
          (Shared.cayleyColorStep (D3EvenRouteEGeSix.colorDir m)
            c ((D3EvenRouteEGeSix.layerRootEquiv m).symm tw)) := by
          unfold finalD3RootFlatModelColorDir
          unfold finalRootFlatModelColorDir
          simp [schedule]
    _ = D3EvenRouteEGeSix.routeEFullStep m c tw := by
          exact D3EvenRouteEGeSix.layerRootEquiv_cayleyColorStep_fullStep
            m c tw
    _ = (schedule m).fullStep c tw := by
          rcases tw with ⟨t, w⟩
          simp [D3EvenRouteEGeSix.routeEFullStep,
            Shared.RootFlatSchedule.fullStep,
            schedule_layerMap_eq_routeELayerMap]
    _ =
        (D3EvenRouteEGeSix.layerRootEquiv m)
          ((D3EvenRouteEGeSix.layerRootEquiv m).symm
            ((schedule m).fullStep c tw)) := by
          simp

theorem rootFlatModel_of_zero_layer_returnMap
    {m : Nat} [NeZero m] (hm3 : 3 ≤ m)
    (hZero :
      ∀ c : Shared.TorusColor 3,
        Function.Bijective
          (D3EvenRouteEGeSix.routeELayerMap m (0 : ZMod m) c))
    (hReturn :
      ∀ c : Shared.TorusColor 3,
        Shared.IsSingleCycleMap (D3EvenRouteEGeSix.routeEReturnMap m c)) :
    FinalD3EvenRootFlatModel m
      (D3EvenRouteEGeSix.RootState m) (schedule m)
      (D3EvenRouteEGeSix.layerRootEquiv m).symm :=
  finalRootFlatTorusModel_of_fields
    (schedule_rowLatin m)
    (schedule_layerBijective_of_zero_layer hm3 hZero)
    (schedule_returnsSingleCycle_of_routeEReturnMap hReturn)
    schedule_stepConjugacy

theorem rootFlatCertificate_of_zero_layer_returnMap
    {m : Nat} [NeZero m] (hm3 : 3 ≤ m)
    (hZero :
      ∀ c : Shared.TorusColor 3,
        Function.Bijective
          (D3EvenRouteEGeSix.routeELayerMap m (0 : ZMod m) c))
    (hReturn :
      ∀ c : Shared.TorusColor 3,
        Shared.IsSingleCycleMap (D3EvenRouteEGeSix.routeEReturnMap m c)) :
    FinalD3EvenRootFlatCertificate m :=
  finalRootFlatTorusCertificate_of_model
    (rootFlatModel_of_zero_layer_returnMap hm3 hZero hReturn)

theorem rootFlatCertificate_of_zero_layer_rankPackage
    {m : Nat} [NeZero m] (_hmEven : Even m) (hm6 : 6 ≤ m)
    (hZero :
      ∀ c : Shared.TorusColor 3,
        Function.Bijective
          (D3EvenRouteEGeSix.routeELayerMap m (0 : ZMod m) c))
    (pkg : D3EvenRouteEGeSix.RouteEReturnModelRankPackage m) :
    FinalD3EvenRootFlatCertificate m :=
  rootFlatCertificate_of_zero_layer_returnMap
    (by omega : 3 ≤ m) hZero
    (D3EvenRouteEGeSix.RouteEReturnModelRankPackage.returnMap_singleCycle
      pkg (by omega : 3 ≤ m))

theorem rootFlatCertificate_of_zero_layer_returnModels
    {m : Nat} [NeZero m] (_hmEven : Even m) (hm6 : 6 ≤ m)
    (hZero :
      ∀ c : Shared.TorusColor 3,
        Function.Bijective
          (D3EvenRouteEGeSix.routeELayerMap m (0 : ZMod m) c))
    (hReturnZero :
      Shared.IsSingleCycleMap (D3EvenRouteEGeSix.routeEReturnZeroModel m))
    (hReturnOne :
      Shared.IsSingleCycleMap (D3EvenRouteEGeSix.routeEReturnOneModel m))
    (hReturnTwo :
      Shared.IsSingleCycleMap (D3EvenRouteEGeSix.routeEReturnTwoModel m)) :
    FinalD3EvenRootFlatCertificate m :=
  rootFlatCertificate_of_zero_layer_returnMap
    (by omega : 3 ≤ m) hZero
    (D3EvenRouteEGeSix.routeEReturnMap_singleCycle_of_models
      (m := m) (by omega : 3 ≤ m)
      hReturnZero hReturnOne hReturnTwo)

theorem rootFlatCertificate_m6 :
    FinalD3EvenRootFlatCertificate 6 :=
  rootFlatCertificate_of_zero_layer_returnMap
    (m := 6) (by norm_num)
    D3EvenRouteEGeSix.routeELayerMap_zero_layer_bijective_m6
    D3EvenRouteEGeSix.routeEReturnMap_singleCycle_m6

theorem rootFlatCertificate_m8 :
    FinalD3EvenRootFlatCertificate 8 :=
  rootFlatCertificate_of_zero_layer_returnMap
    (m := 8) (by norm_num)
    D3EvenRouteEGeSix.routeELayerMap_zero_layer_bijective_m8
    D3EvenRouteEGeSix.routeEReturnMap_singleCycle_m8

theorem rootFlatCertificate_m10 :
    FinalD3EvenRootFlatCertificate 10 :=
  rootFlatCertificate_of_zero_layer_returnMap
    (m := 10) (by norm_num)
    D3EvenRouteEGeSix.routeELayerMap_zero_layer_bijective_m10
    D3EvenRouteEGeSix.routeEReturnMap_singleCycle_m10

theorem rootFlatCertificate_m12 :
    FinalD3EvenRootFlatCertificate 12 :=
  rootFlatCertificate_of_zero_layer_returnMap
    (m := 12) (by norm_num)
    D3EvenRouteEGeSix.routeELayerMap_zero_layer_bijective_m12
    D3EvenRouteEGeSix.routeEReturnMap_singleCycle_m12

theorem rootFlatCertificateFamily_of_m4_zero_layer_rankPackage
    (m4 : FinalD3EvenRootFlatCertificate 4)
    (hZero :
      ∀ {m : Nat} [NeZero m], Even m → 6 ≤ m →
        ∀ c : Shared.TorusColor 3,
          Function.Bijective
            (D3EvenRouteEGeSix.routeELayerMap m (0 : ZMod m) c))
    (hRank :
      ∀ {m : Nat} [NeZero m], Even m → 6 ≤ m →
        D3EvenRouteEGeSix.RouteEReturnModelRankPackage m) :
    FinalD3EvenRootFlatCertificateFamily where
  rootFlatCertificate := by
    intro m hm
    rcases hm with ⟨hm4, k, rfl⟩
    by_cases hk : k = 2
    · subst k
      simpa using m4
    · haveI : NeZero (2 * k) := ⟨by omega⟩
      have hEven : Even (2 * k) := ⟨k, by omega⟩
      have hSix : 6 ≤ 2 * k := by omega
      exact rootFlatCertificate_of_zero_layer_rankPackage
        (m := 2 * k) hEven hSix
        (hZero hEven hSix)
        (hRank hEven hSix)

theorem rootFlatCertificateFamily_of_m4_zero_layer_returnModels
    (m4 : FinalD3EvenRootFlatCertificate 4)
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
    FinalD3EvenRootFlatCertificateFamily where
  rootFlatCertificate := by
    intro m hm
    rcases hm with ⟨hm4, k, rfl⟩
    by_cases hk : k = 2
    · subst k
      simpa using m4
    · haveI : NeZero (2 * k) := ⟨by omega⟩
      have hEven : Even (2 * k) := ⟨k, by omega⟩
      have hSix : 6 ≤ 2 * k := by omega
      exact rootFlatCertificate_of_zero_layer_returnModels
        (m := 2 * k) hEven hSix
        (hZero hEven hSix)
        (hReturnZero hEven hSix)
        (hReturnOne hEven hSix)
        (hReturnTwo hEven hSix)

end D3EvenRouteERootFlatBridge
end EvenV11
