-- STATUS: main-path (colour 3: the terminal splice gives a single-cycle return)
import TorusEven.D5.Endpoint1
import TorusEven.D5.Terminal1

/-!
# Colour `3` (terminal index `i = 1`, direction `0`, functional `ℓ_1 = b`)
-/

namespace TorusEven
namespace D5

open Cert D5Data Chronological

variable {m : ℕ} [NeZero m]

theorem stageLayer_c3_three (t : ℕ) : stageLayer (m := m) (3 : Fin 5) 3 t = stageLayer 3 2 t := by
  funext x
  unfold stageLayer
  by_cases h2 : t = 2
  · subst h2
    simp [corr, rowOf]
  · have : (t < 3) ↔ (t < 2) := by omega
    simp only [this]

section colour3

variable (h6 : 6 ≤ m) (hm : Even m)
include h6 hm

theorem f3_phi (q : Pt m) : fval f_c3 (phi q) = -q.2 := by
  simp [fval, f_c3, phi, Fin.sum_univ_four]

/-- `K_3 = ker f_3`, the final chain module of colour `3`. -/
theorem mem_coset_K3_iff (x y : Root m) :
    y ∈ coset (colSpan (castM (m := m) Hz_c3p2next)) x ↔ fval f_c3 y = fval f_c3 x := by
  rw [← final_c3, mem_coset_kerOf_rowM_iff]

/-! `N_1 ∘ j_1` is a bijection of `B_1`. -/

theorem NJ1_iterate_inB (n : ℕ) : inB 1 (NJ1^[n] (ptA : Pt m)) := by
  induction n with
  | zero => exact inB_of_fam1 h6 (Or.inl rfl)
  | succ n ih => rw [Function.iterate_succ_apply']; exact NJ1_inB h6 hm ih

theorem NJ1_surj {w : Pt m} (hw : inB 1 w) : ∃ q, inB 1 q ∧ NJ1 q = w := by
  obtain ⟨k, hk⟩ := NJ1_orbit_covers h6 hm hw
  rcases k with _ | k
  · have hc := consts h6
    refine ⟨ptY 3, inB_of_fam1 h6 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.1⟩))))))), ?_⟩
    rw [NJ1_Y3 h6]
    exact hk
  · refine ⟨NJ1^[k] ptA, NJ1_iterate_inB h6 hm k, ?_⟩
    simpa [Function.iterate_succ_apply'] using hk

theorem NJ1_inj {q q' : Pt m} (hq : inB 1 q) (hq' : inB 1 q') (h : NJ1 q = NJ1 q') : q = q' := by
  let f : {q : Pt m // inB 1 q} → {q : Pt m // inB 1 q} := fun q => ⟨NJ1 q.1, NJ1_inB h6 hm q.2⟩
  have hsurj : Function.Surjective f := by
    intro w
    obtain ⟨q, hq, hqw⟩ := NJ1_surj h6 hm w.2
    exact ⟨⟨q, hq⟩, Subtype.ext hqw⟩
  have hinj : Function.Injective f := Finite.injective_iff_surjective.2 hsurj
  have := @hinj ⟨q, hq⟩ ⟨q', hq'⟩ (Subtype.ext h)
  exact congrArg Subtype.val this

theorem jmap1_inj {q q' : Pt m} (hq : inB 1 q) (hq' : inB 1 q') (h : jmap 1 q = jmap 1 q') :
    q = q' :=
  NJ1_inj h6 hm hq hq' (by unfold NJ1; rw [h])

/-- The terminal splice for colour `3`. -/
theorem terminal_c3 (S : Equiv.Perm (Root m))
    (hS : ∀ x, Surgery.orbitSet S x = coset (colSpan (castM (m := m) Hz_c3p2next)) x) :
    Shared.IsSingleCycleMap (fun x => S (Jplane (dirs 1) x)) := by
  have hj : ∀ q : Pt m, inB 1 q → inB 1 (jmap 1 q) := fun q hq => jmap1_inB h6 hm hq
  refine TerminalSplice.single_cycle S _ hS (Uset 1) (Jplane (dirs 1))
    (Jplane_bijective 1 hj (fun q q' hq hq' h => jmap1_inj h6 hm hq hq' h))
    (fun x hx => Jplane_of_not_mem 1 hx) (fun x hx => Jplane_mem 1 hj hx)
    ?_ (fun w => phi (partner1 (planePoint w))) ?_ ?_ ?_ ?_ (phi ptA)
    (phi_mem_Uset.2 (inB_of_fam1 h6 (Or.inl rfl))) ?_
  · intro x
    obtain ⟨q, hq, hq2⟩ := fibre1_exists h6 hm (-(fval f_c3 x))
    exact ⟨phi q, phi_mem_Uset.2 hq, by rw [mem_coset_K3_iff h6 hm, f3_phi h6 hm, hq2, neg_neg]⟩
  · intro w hw
    obtain ⟨q, hq, rfl⟩ := mem_Uset_iff.1 hw
    dsimp only
    rw [planePoint_phi]
    exact phi_mem_Uset.2 (partner1_inB h6 hm hq)
  · intro w hw
    obtain ⟨q, hq, rfl⟩ := mem_Uset_iff.1 hw
    dsimp only
    rw [planePoint_phi]
    intro h
    exact partner1_ne h6 hm hq (phi_injective h)
  · intro w hw
    obtain ⟨q, hq, rfl⟩ := mem_Uset_iff.1 hw
    dsimp only
    rw [planePoint_phi, mem_coset_K3_iff h6 hm, f3_phi h6 hm, f3_phi h6 hm, partner1_snd]
  · intro w hw y hy hyw
    obtain ⟨q, hq, rfl⟩ := mem_Uset_iff.1 hw
    obtain ⟨q', hq', rfl⟩ := mem_Uset_iff.1 hy
    rw [mem_coset_K3_iff h6 hm, f3_phi h6 hm, f3_phi h6 hm] at hyw
    dsimp only
    rw [planePoint_phi]
    rcases fibre1_unique h6 hm hq hq' (neg_inj.1 hyw) with h | h
    · left; rw [h]
    · right; rw [h]
  · intro w hw
    obtain ⟨q, hq, rfl⟩ := mem_Uset_iff.1 hw
    obtain ⟨k, hk⟩ := NJ1_orbit_covers h6 hm hq
    refine ⟨k, ?_⟩
    have hiter : ∀ n, (fun y : Root m => phi (partner1 (planePoint (Jplane (dirs 1) y))))^[n]
        (phi (ptA : Pt m)) = phi (NJ1^[n] (ptA : Pt m)) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [Function.iterate_succ_apply', ih, Jplane_phi, planePoint_phi,
            Function.iterate_succ_apply']
          rfl
    rw [hiter, hk]

/-! ### Back to the schedule -/

theorem orbits_c3_final (x : Root m) :
    Chronological.orbitSet (Layers.pre (stageLayer (3 : Fin 5) 3) m) x =
      coset (colSpan (castM (m := m) Hz_c3p2next)) x := by
  have : stageLayer (m := m) (3 : Fin 5) 3 = stageLayer 3 2 := funext stageLayer_c3_three
  rw [this]
  exact orbits_c3_2 h6 x

/-- The actual layers of colour `3` in the schedule. -/
def actual3 (m : ℕ) [NeZero m] (t : ℕ) : Root m → Root m :=
  (schedule m).layerMap ((t : ℕ) : ZMod m) 3

theorem actual3_eq (t : ℕ) (ht : t < m) (ht2 : t ≠ 2) : actual3 m t = stageLayer 3 3 t := by
  rw [← preLayer_eq_stage]
  funext x
  rcases t with _ | _ | _ | t
  · exact layer_c3_t0 h6 x
  · exact layer_c3_t1 h6 x
  · exact absurd rfl ht2
  · exact layer_ge3 h6 (by omega) ht 3 x

theorem actual3_two : actual3 m 2 = stageLayer 3 3 2 ∘ Jplane (dirs 1) := by
  funext x
  rw [← preLayer_eq_stage]
  exact layer_terminal h6 3 (Or.inr (Or.inl rfl)) x

theorem prefix_c3 (x : Root m) :
    Layers.pre (stageLayer (3 : Fin 5) 3) 2 x - x - (∑ s ∈ Finset.range 2, uvec (neut 3 s)) ∈
      colSpan (castM (m := m) Hz_c3p2next) := by
  apply prefix_stage
  intro s hs P e hrow
  interval_cases s <;> simp [rowOf] at hrow <;> obtain ⟨rfl, rfl⟩ := hrow
  · exact mem_c3p1_in_2_c3
  · exact mem_c3p2_in_2_c3

theorem returnMap_single_cycle_c3 : Shared.IsSingleCycleMap ((schedule m).returnMap 3) := by
  let S₀ : Equiv.Perm (Root m) :=
    Equiv.ofBijective _ (Layers.pre_bijective _ (stageLayer_bijective (3 : Fin 5) 3) m)
  let P : Equiv.Perm (Root m) :=
    Equiv.ofBijective _ (Layers.pre_bijective _ (stageLayer_bijective (3 : Fin 5) 3) 2)
  have hPeq : ⇑P = Layers.pre (stageLayer 3 3) 2 := rfl
  have hS₀eq : ⇑S₀ = Layers.pre (stageLayer 3 3) m := rfl
  have hret : (schedule m).returnMap 3 =
      Layers.pre (stageLayer 3 3) m ∘ (P.symm ∘ Jplane (dirs 1) ∘ P) := by
    rw [returnMap_eq_pre]
    exact Layers.pre_change (stageLayer 3 3) (actual3 m) 2 m (by omega) (Jplane (dirs 1))
      (fun s hs hsm => actual3_eq h6 hm s hsm hs) (actual3_two h6 hm) P hPeq
  let S : Equiv.Perm (Root m) := (P.symm.trans S₀).trans P
  have hS : ∀ x, Chronological.orbitSet S x = coset (colSpan (castM (m := m) Hz_c3p2next)) x :=
    orbitSet_conj_coset S₀ P _ (by simpa [hS₀eq] using orbits_c3_final h6 hm) _
      (by simpa [hPeq] using prefix_c3 h6 hm)
  have hSJ := terminal_c3 h6 hm S hS
  refine Shared.single_cycle_of_equiv_conj P.symm ((schedule m).returnMap 3)
    (fun x => S (Jplane (dirs 1) x)) hSJ ?_
  intro x
  rw [hret]
  simp only [Function.comp, Equiv.symm_symm, Equiv.apply_symm_apply]
  rfl

end colour3

end D5
end TorusEven
