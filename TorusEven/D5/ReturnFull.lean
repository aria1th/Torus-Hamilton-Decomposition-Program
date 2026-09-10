-- STATUS: main-path (colours 0 and 2: the preterminal return is already Hamilton)
import TorusEven.D5.Preterminal

/-!
# Colours `0` and `2`

Their chains end at the whole root space, so the return map of the schedule is a single
`m^4`-cycle (manuscript: "colours `0, 2` have one root-return cycle of length `m^4`").
-/

namespace TorusEven
namespace D5

open Cert D5Data Chronological

variable {m : ℕ} [NeZero m]

/-- The return map of the schedule is the fold of the schedule's layers. -/
theorem returnMap_eq_pre (c : Fin 5) :
    (schedule m).returnMap c =
      Layers.pre (fun t => (schedule m).layerMap ((t : ℕ) : ZMod m) c) m := by
  funext x
  rw [Layers.pre_eq_foldl]
  rfl

/-- For colours `0, 2` every layer of the schedule is the final-stage layer. -/
theorem layer_eq_stage3_full (hm : 6 ≤ m) (c : Fin 5) (hc : c = 0 ∨ c = 2) (t : ℕ) (ht : t < m) :
    (schedule m).layerMap ((t : ℕ) : ZMod m) c = stageLayer c 3 t := by
  rw [← preLayer_eq_stage]
  funext x
  rcases t with _ | _ | _ | t
  · rcases hc with rfl | rfl
    · exact layer_c0_t0 hm x
    · exact layer_c2_t0 hm x
  · rcases hc with rfl | rfl
    · exact layer_c0_t1 hm x
    · exact layer_c2_t1 hm x
  · rcases hc with rfl | rfl
    · exact layer_c0_t2 hm x
    · exact layer_c2_t2 hm x
  · exact layer_ge3 hm (by omega) ht c x

theorem pre_congr_lt (L L' : ℕ → Root m → Root m) (n : ℕ) (h : ∀ t, t < n → L t = L' t) :
    Layers.pre L n = Layers.pre L' n :=
  Layers.pre_congr L' L n (fun s hs => h s hs)

theorem returnMap_eq_stage3_full (hm : 6 ≤ m) (c : Fin 5) (hc : c = 0 ∨ c = 2) :
    (schedule m).returnMap c = Layers.pre (stageLayer c 3) m := by
  rw [returnMap_eq_pre]
  exact pre_congr_lt _ _ m (fun t ht => layer_eq_stage3_full hm c hc t ht)

theorem orbits_univ_c0 (hm : 6 ≤ m) (x : Root m) :
    Chronological.orbitSet (Layers.pre (stageLayer (0 : Fin 5) 3) m) x = Set.univ := by
  rw [orbits_c0_3 hm, final_c0]
  ext y
  simp [coset_def']

theorem orbits_univ_c2 (hm : 6 ≤ m) (x : Root m) :
    Chronological.orbitSet (Layers.pre (stageLayer (2 : Fin 5) 3) m) x = Set.univ := by
  rw [orbits_c2_3 hm, final_c2]
  ext y
  simp [coset_def']

theorem returnMap_single_cycle_c0 (hm : 6 ≤ m) :
    Shared.IsSingleCycleMap ((schedule m).returnMap 0) := by
  rw [returnMap_eq_stage3_full hm 0 (Or.inl rfl)]
  exact Surgery.single_cycle_of_orbitSet_univ
    (Layers.pre_bijective _ (stageLayer_bijective 0 3) m) 0 (orbits_univ_c0 hm 0)

theorem returnMap_single_cycle_c2 (hm : 6 ≤ m) :
    Shared.IsSingleCycleMap ((schedule m).returnMap 2) := by
  rw [returnMap_eq_stage3_full hm 2 (Or.inr rfl)]
  exact Surgery.single_cycle_of_orbitSet_univ
    (Layers.pre_bijective _ (stageLayer_bijective 2 3) m) 0 (orbits_univ_c2 hm 0)

end D5
end TorusEven
