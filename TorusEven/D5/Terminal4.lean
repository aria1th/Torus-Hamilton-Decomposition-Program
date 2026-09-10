-- STATUS: main-path (colour 4: the terminal splice gives a single-cycle return)
import TorusEven.D5.Endpoint2
import TorusEven.D5.Terminal1

/-!
# Colour `4` (terminal index `i = 2`, direction `1`, functional `ℓ_2 = a + b`)
-/

namespace TorusEven
namespace D5

open Cert D5Data Chronological

variable {m : ℕ} [NeZero m]

theorem stageLayer_c4_three (t : ℕ) : stageLayer (m := m) (4 : Fin 5) 3 t = stageLayer 4 2 t := by
  funext x
  unfold stageLayer
  by_cases h2 : t = 2
  · subst h2
    simp [corr, rowOf]
  · have : (t < 3) ↔ (t < 2) := by omega
    simp only [this]

section colour4

variable (h6 : 6 ≤ m) (hm : Even m)
include h6 hm

theorem f4_phi (q : Pt m) : fval f_c4 (phi q) = q.1 + q.2 := by
  simp [fval, f_c4, phi, Fin.sum_univ_four]
  ring

/-- `K_4 = ker f_4`, the final chain module of colour `4`. -/
theorem mem_coset_K4_iff (x y : Root m) :
    y ∈ coset (colSpan (castM (m := m) Hz_c4p2next)) x ↔ fval f_c4 y = fval f_c4 x := by
  rw [← final_c4, mem_coset_kerOf_rowM_iff]

/-! `N_2 ∘ j_2` is a bijection of `B_2`. -/

theorem NJ2_iterate_inB (n : ℕ) : inB 2 (NJ2^[n] (ptA : Pt m)) := by
  induction n with
  | zero => exact inB_of_fam2 h6 (Or.inl rfl)
  | succ n ih => rw [Function.iterate_succ_apply']; exact NJ2_inB h6 hm ih

theorem NJ2_surj {w : Pt m} (hw : inB 2 w) : ∃ q, inB 2 q ∧ NJ2 q = w := by
  obtain ⟨k, hk⟩ := NJ2_orbit_covers h6 hm hw
  rcases k with _ | k
  · have hc := consts h6
    refine ⟨ptY 0, inB_of_fam2 h6 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hc.2.2.1⟩)))), ?_⟩
    rw [NJ2_Y0 h6]
    exact hk
  · refine ⟨NJ2^[k] ptA, NJ2_iterate_inB h6 hm k, ?_⟩
    simpa [Function.iterate_succ_apply'] using hk

theorem NJ2_inj {q q' : Pt m} (hq : inB 2 q) (hq' : inB 2 q') (h : NJ2 q = NJ2 q') : q = q' := by
  let f : {q : Pt m // inB 2 q} → {q : Pt m // inB 2 q} := fun q => ⟨NJ2 q.1, NJ2_inB h6 hm q.2⟩
  have hsurj : Function.Surjective f := by
    intro w
    obtain ⟨q, hq, hqw⟩ := NJ2_surj h6 hm w.2
    exact ⟨⟨q, hq⟩, Subtype.ext hqw⟩
  have hinj : Function.Injective f := Finite.injective_iff_surjective.2 hsurj
  have := @hinj ⟨q, hq⟩ ⟨q', hq'⟩ (Subtype.ext h)
  exact congrArg Subtype.val this

theorem jmap2_inj {q q' : Pt m} (hq : inB 2 q) (hq' : inB 2 q') (h : jmap 2 q = jmap 2 q') :
    q = q' :=
  NJ2_inj h6 hm hq hq' (by unfold NJ2; rw [h])

/-- The terminal splice for colour `4`. -/
theorem terminal_c4 (S : Equiv.Perm (Root m))
    (hS : ∀ x, Surgery.orbitSet S x = coset (colSpan (castM (m := m) Hz_c4p2next)) x) :
    Shared.IsSingleCycleMap (fun x => S (Jplane (dirs 2) x)) := by
  have hj : ∀ q : Pt m, inB 2 q → inB 2 (jmap 2 q) := fun q hq => jmap2_inB h6 hm hq
  refine TerminalSplice.single_cycle S _ hS (Uset 2) (Jplane (dirs 2))
    (Jplane_bijective 2 hj (fun q q' hq hq' h => jmap2_inj h6 hm hq hq' h))
    (fun x hx => Jplane_of_not_mem 2 hx) (fun x hx => Jplane_mem 2 hj hx)
    ?_ (fun w => phi (partner2 (planePoint w))) ?_ ?_ ?_ ?_ (phi ptA)
    (phi_mem_Uset.2 (inB_of_fam2 h6 (Or.inl rfl))) ?_
  · intro x
    obtain ⟨q, hq, hq2⟩ := fibre2_exists h6 hm (fval f_c4 x)
    exact ⟨phi q, phi_mem_Uset.2 hq, by rw [mem_coset_K4_iff h6 hm, f4_phi h6 hm, hq2]⟩
  · intro w hw
    obtain ⟨q, hq, rfl⟩ := mem_Uset_iff.1 hw
    dsimp only
    rw [planePoint_phi]
    exact phi_mem_Uset.2 (partner2_inB h6 hm hq)
  · intro w hw
    obtain ⟨q, hq, rfl⟩ := mem_Uset_iff.1 hw
    dsimp only
    rw [planePoint_phi]
    intro h
    exact partner2_ne h6 hm hq (phi_injective h)
  · intro w hw
    obtain ⟨q, hq, rfl⟩ := mem_Uset_iff.1 hw
    dsimp only
    rw [planePoint_phi, mem_coset_K4_iff h6 hm, f4_phi h6 hm, f4_phi h6 hm, partner2_sum]
  · intro w hw y hy hyw
    obtain ⟨q, hq, rfl⟩ := mem_Uset_iff.1 hw
    obtain ⟨q', hq', rfl⟩ := mem_Uset_iff.1 hy
    rw [mem_coset_K4_iff h6 hm, f4_phi h6 hm, f4_phi h6 hm] at hyw
    dsimp only
    rw [planePoint_phi]
    rcases fibre2_unique h6 hm hq hq' hyw with h | h
    · left; rw [h]
    · right; rw [h]
  · intro w hw
    obtain ⟨q, hq, rfl⟩ := mem_Uset_iff.1 hw
    obtain ⟨k, hk⟩ := NJ2_orbit_covers h6 hm hq
    refine ⟨k, ?_⟩
    have hiter : ∀ n, (fun y : Root m => phi (partner2 (planePoint (Jplane (dirs 2) y))))^[n]
        (phi (ptA : Pt m)) = phi (NJ2^[n] (ptA : Pt m)) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [Function.iterate_succ_apply', ih, Jplane_phi, planePoint_phi,
            Function.iterate_succ_apply']
          rfl
    rw [hiter, hk]

/-! ### Back to the schedule -/

theorem orbits_c4_final (x : Root m) :
    Chronological.orbitSet (Layers.pre (stageLayer (4 : Fin 5) 3) m) x =
      coset (colSpan (castM (m := m) Hz_c4p2next)) x := by
  have : stageLayer (m := m) (4 : Fin 5) 3 = stageLayer 4 2 := funext stageLayer_c4_three
  rw [this]
  exact orbits_c4_2 h6 x

/-- The actual layers of colour `4` in the schedule. -/
def actual4 (m : ℕ) [NeZero m] (t : ℕ) : Root m → Root m :=
  (schedule m).layerMap ((t : ℕ) : ZMod m) 4

theorem actual4_eq (t : ℕ) (ht : t < m) (ht2 : t ≠ 2) : actual4 m t = stageLayer 4 3 t := by
  rw [← preLayer_eq_stage]
  funext x
  rcases t with _ | _ | _ | t
  · exact layer_c4_t0 h6 x
  · exact layer_c4_t1 h6 x
  · exact absurd rfl ht2
  · exact layer_ge3 h6 (by omega) ht 4 x

theorem actual4_two : actual4 m 2 = stageLayer 4 3 2 ∘ Jplane (dirs 2) := by
  funext x
  rw [← preLayer_eq_stage]
  exact layer_terminal h6 4 (Or.inr (Or.inr rfl)) x

theorem prefix_c4 (x : Root m) :
    Layers.pre (stageLayer (4 : Fin 5) 3) 2 x - x - (∑ s ∈ Finset.range 2, uvec (neut 4 s)) ∈
      colSpan (castM (m := m) Hz_c4p2next) := by
  apply prefix_stage
  intro s hs P e hrow
  interval_cases s <;> simp [rowOf] at hrow <;> obtain ⟨rfl, rfl⟩ := hrow
  · exact mem_c4p1_in_2_c4
  · exact mem_c4p2_in_2_c4

theorem returnMap_single_cycle_c4 : Shared.IsSingleCycleMap ((schedule m).returnMap 4) := by
  let S₀ : Equiv.Perm (Root m) :=
    Equiv.ofBijective _ (Layers.pre_bijective _ (stageLayer_bijective (4 : Fin 5) 3) m)
  let P : Equiv.Perm (Root m) :=
    Equiv.ofBijective _ (Layers.pre_bijective _ (stageLayer_bijective (4 : Fin 5) 3) 2)
  have hPeq : ⇑P = Layers.pre (stageLayer 4 3) 2 := rfl
  have hS₀eq : ⇑S₀ = Layers.pre (stageLayer 4 3) m := rfl
  have hret : (schedule m).returnMap 4 =
      Layers.pre (stageLayer 4 3) m ∘ (P.symm ∘ Jplane (dirs 2) ∘ P) := by
    rw [returnMap_eq_pre]
    exact Layers.pre_change (stageLayer 4 3) (actual4 m) 2 m (by omega) (Jplane (dirs 2))
      (fun s hs hsm => actual4_eq h6 hm s hsm hs) (actual4_two h6 hm) P hPeq
  let S : Equiv.Perm (Root m) := (P.symm.trans S₀).trans P
  have hS : ∀ x, Chronological.orbitSet S x = coset (colSpan (castM (m := m) Hz_c4p2next)) x :=
    orbitSet_conj_coset S₀ P _ (by simpa [hS₀eq] using orbits_c4_final h6 hm) _
      (by simpa [hPeq] using prefix_c4 h6 hm)
  have hSJ := terminal_c4 h6 hm S hS
  refine Shared.single_cycle_of_equiv_conj P.symm ((schedule m).returnMap 4)
    (fun x => S (Jplane (dirs 2) x)) hSJ ?_
  intro x
  rw [hret]
  simp only [Function.comp, Equiv.symm_symm, Equiv.apply_symm_apply]
  rfl

end colour4

end D5
end TorusEven
