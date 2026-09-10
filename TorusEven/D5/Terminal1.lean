-- STATUS: main-path (colour 1: the terminal splice gives a single-cycle return)
import TorusEven.D5.PlaneChart
import TorusEven.D5.Terminal
import TorusEven.D5.ReturnFull

/-!
# Colour `1` (terminal index `i = 0`, direction `3`)
-/

namespace TorusEven
namespace D5

open Cert D5Data Chronological

variable {m : ℕ} [NeZero m]

/-- The character value `f · v`. -/
def fval (f : Fin 4 → ℤ) (v : Root m) : ZMod m := ∑ j, ((f j : ℤ) : ZMod m) * v j

theorem fval_sub (f : Fin 4 → ℤ) (v w : Root m) : fval f (v - w) = fval f v - fval f w := by
  simp [fval, Finset.sum_sub_distrib, mul_sub]

theorem mem_coset_kerOf_rowM_iff (f : Fin 4 → ℤ) (x y : Root m) :
    y ∈ coset (kerOf (castM (m := m) (rowM f))) x ↔ fval f y = fval f x := by
  rw [coset_def', mem_kerOf_rowM]
  show fval f (y - x) = 0 ↔ _
  rw [fval_sub, sub_eq_zero]

/-- The orbits of a conjugate `P ∘ S₀ ∘ P⁻¹`, when `P` is a translation modulo `K`. -/
theorem orbitSet_conj_coset (S₀ P : Equiv.Perm (Root m)) (K : AddSubgroup (Root m))
    (hS : ∀ x, Chronological.orbitSet S₀ x = coset K x) (b : Root m) (hP : ∀ x, P x - x - b ∈ K) (y : Root m) :
    Chronological.orbitSet ((P.symm.trans S₀).trans P) y = coset K y := by
  have hiter : ∀ n x, ((P.symm.trans S₀).trans P)^[n] x = P (S₀^[n] (P.symm x)) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
        simp
  ext z
  rw [coset_def']
  constructor
  · rintro ⟨n, rfl⟩
    dsimp only
    rw [hiter]
    have h1 : S₀^[n] (P.symm y) ∈ Chronological.orbitSet S₀ (P.symm y) := ⟨n, rfl⟩
    rw [hS, coset_def'] at h1
    have h2 := hP (S₀^[n] (P.symm y))
    have h3 := hP (P.symm y)
    rw [Equiv.apply_symm_apply] at h3
    have : P (S₀^[n] (P.symm y)) - y =
        (P (S₀^[n] (P.symm y)) - S₀^[n] (P.symm y) - b) + (S₀^[n] (P.symm y) - P.symm y) -
          (y - P.symm y - b) := by abel
    rw [this]
    exact K.sub_mem (K.add_mem h2 h1) h3
  · intro hz
    have h1 : P.symm z ∈ Chronological.orbitSet S₀ (P.symm y) := by
      rw [hS, coset_def']
      have h2 := hP (P.symm z)
      have h3 := hP (P.symm y)
      rw [Equiv.apply_symm_apply] at h2 h3
      have : P.symm z - P.symm y = (z - y) - (z - P.symm z - b) + (y - P.symm y - b) := by abel
      rw [this]
      exact K.add_mem (K.sub_mem hz h2) h3
    obtain ⟨n, hn⟩ := h1
    refine ⟨n, ?_⟩
    dsimp only at hn ⊢
    rw [hiter, hn, Equiv.apply_symm_apply]

theorem stageLayer_c1_three (t : ℕ) : stageLayer (m := m) (1 : Fin 5) 3 t = stageLayer 1 2 t := by
  funext x
  unfold stageLayer
  by_cases h2 : t = 2
  · subst h2
    simp [corr, rowOf]
  · have : (t < 3) ↔ (t < 2) := by omega
    simp only [this]

section colour1

variable (h6 : 6 ≤ m) (hm : Even m)
include h6 hm

theorem f1_phi (q : Pt m) : fval f_c1 (phi q) = q.1 := by
  simp [fval, f_c1, phi, Fin.sum_univ_four]
  ring

/-- `K_1 = ker f_1`, the final chain module of colour `1`. -/
theorem mem_coset_K1_iff (x y : Root m) :
    y ∈ coset (colSpan (castM (m := m) Hz_c1p3next)) x ↔ fval f_c1 y = fval f_c1 x := by
  rw [← final_c1, mem_coset_kerOf_rowM_iff]

/-! `N_0 ∘ j_0` is a bijection of `B_0`. -/

theorem NJ0_iterate_inB (n : ℕ) : inB 0 (NJ0^[n] (ptA : Pt m)) := by
  induction n with
  | zero => exact inB_of_fam0 h6 (Or.inl rfl)
  | succ n ih => rw [Function.iterate_succ_apply']; exact NJ0_inB h6 hm ih

theorem NJ0_surj {w : Pt m} (hw : inB 0 w) : ∃ q, inB 0 q ∧ NJ0 q = w := by
  obtain ⟨k, hk⟩ := NJ0_orbit_covers h6 hm hw
  rcases k with _ | k
  · refine ⟨ptY 3, inB_of_fam0 h6 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), ?_⟩
    rw [NJ0_Y3 h6]
    exact hk
  · refine ⟨NJ0^[k] ptA, NJ0_iterate_inB h6 hm k, ?_⟩
    simpa [Function.iterate_succ_apply'] using hk

theorem NJ0_inj {q q' : Pt m} (hq : inB 0 q) (hq' : inB 0 q') (h : NJ0 q = NJ0 q') : q = q' := by
  let f : {q : Pt m // inB 0 q} → {q : Pt m // inB 0 q} := fun q => ⟨NJ0 q.1, NJ0_inB h6 hm q.2⟩
  have hsurj : Function.Surjective f := by
    intro w
    obtain ⟨q, hq, hqw⟩ := NJ0_surj h6 hm w.2
    exact ⟨⟨q, hq⟩, Subtype.ext hqw⟩
  have hinj : Function.Injective f := Finite.injective_iff_surjective.2 hsurj
  have := @hinj ⟨q, hq⟩ ⟨q', hq'⟩ (Subtype.ext h)
  exact congrArg Subtype.val this

theorem jmap0_inj {q q' : Pt m} (hq : inB 0 q) (hq' : inB 0 q') (h : jmap 0 q = jmap 0 q') :
    q = q' :=
  NJ0_inj h6 hm hq hq' (by unfold NJ0; rw [h])

/-- The terminal splice for colour `1`. -/
theorem terminal_c1 (S : Equiv.Perm (Root m))
    (hS : ∀ x, Surgery.orbitSet S x = coset (colSpan (castM (m := m) Hz_c1p3next)) x) :
    Shared.IsSingleCycleMap (fun x => S (Jplane (dirs 0) x)) := by
  have hj : ∀ q : Pt m, inB 0 q → inB 0 (jmap 0 q) := fun q hq => jmap0_inB h6 hm hq
  refine TerminalSplice.single_cycle S _ hS (Uset 0) (Jplane (dirs 0))
    (Jplane_bijective 0 hj (fun q q' hq hq' h => jmap0_inj h6 hm hq hq' h))
    (fun x hx => Jplane_of_not_mem 0 hx) (fun x hx => Jplane_mem 0 hj hx)
    ?_ (fun w => phi (partner0 (planePoint w))) ?_ ?_ ?_ ?_ (phi ptA)
    (phi_mem_Uset.2 (inB_of_fam0 h6 (Or.inl rfl))) ?_
  · intro x
    obtain ⟨q, hq, hq1⟩ := fibre0_exists h6 hm (fval f_c1 x)
    exact ⟨phi q, phi_mem_Uset.2 hq, by rw [mem_coset_K1_iff h6 hm, f1_phi h6 hm, hq1]⟩
  · intro w hw
    obtain ⟨q, hq, rfl⟩ := mem_Uset_iff.1 hw
    dsimp only
    rw [planePoint_phi]
    exact phi_mem_Uset.2 (partner0_inB h6 hm hq)
  · intro w hw
    obtain ⟨q, hq, rfl⟩ := mem_Uset_iff.1 hw
    dsimp only
    rw [planePoint_phi]
    intro h
    exact partner0_ne h6 hm hq (phi_injective h)
  · intro w hw
    obtain ⟨q, hq, rfl⟩ := mem_Uset_iff.1 hw
    dsimp only
    rw [planePoint_phi, mem_coset_K1_iff h6 hm, f1_phi h6 hm, f1_phi h6 hm, partner0_fst]
  · intro w hw y hy hyw
    obtain ⟨q, hq, rfl⟩ := mem_Uset_iff.1 hw
    obtain ⟨q', hq', rfl⟩ := mem_Uset_iff.1 hy
    rw [mem_coset_K1_iff h6 hm, f1_phi h6 hm, f1_phi h6 hm] at hyw
    dsimp only
    rw [planePoint_phi]
    rcases fibre0_unique h6 hm hq hq' hyw with h | h
    · left; rw [h]
    · right; rw [h]
  · intro w hw
    obtain ⟨q, hq, rfl⟩ := mem_Uset_iff.1 hw
    obtain ⟨k, hk⟩ := NJ0_orbit_covers h6 hm hq
    refine ⟨k, ?_⟩
    have hiter : ∀ n, (fun y : Root m => phi (partner0 (planePoint (Jplane (dirs 0) y))))^[n]
        (phi (ptA : Pt m)) = phi (NJ0^[n] (ptA : Pt m)) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [Function.iterate_succ_apply', ih, Jplane_phi, planePoint_phi,
            Function.iterate_succ_apply']
          rfl
    rw [hiter, hk]

/-! ### Back to the schedule -/

theorem orbits_c1_final (x : Root m) :
    Chronological.orbitSet (Layers.pre (stageLayer (1 : Fin 5) 3) m) x =
      coset (colSpan (castM (m := m) Hz_c1p3next)) x := by
  have : stageLayer (m := m) (1 : Fin 5) 3 = stageLayer 1 2 := funext stageLayer_c1_three
  rw [this]
  exact orbits_c1_2 h6 x

/-- The actual layers of colour `1` in the schedule. -/
def actual1 (m : ℕ) [NeZero m] (t : ℕ) : Root m → Root m :=
  (schedule m).layerMap ((t : ℕ) : ZMod m) 1

theorem actual1_eq (t : ℕ) (ht : t < m) (ht2 : t ≠ 2) : actual1 m t = stageLayer 1 3 t := by
  rw [← preLayer_eq_stage]
  funext x
  rcases t with _ | _ | _ | t
  · exact layer_c1_t0 h6 x
  · exact layer_c1_t1 h6 x
  · exact absurd rfl ht2
  · exact layer_ge3 h6 (by omega) ht 1 x

theorem actual1_two : actual1 m 2 = stageLayer 1 3 2 ∘ Jplane (dirs 0) := by
  funext x
  rw [← preLayer_eq_stage]
  exact layer_terminal h6 1 (Or.inl rfl) x

theorem prefix_c1 (x : Root m) :
    Layers.pre (stageLayer (1 : Fin 5) 3) 2 x - x - (∑ s ∈ Finset.range 2, uvec (neut 1 s)) ∈
      colSpan (castM (m := m) Hz_c1p3next) := by
  apply prefix_stage
  intro s hs P e hrow
  interval_cases s <;> simp [rowOf] at hrow <;> obtain ⟨rfl, rfl⟩ := hrow
  · exact mem_c1p0_in_2_c1
  · exact mem_c1p3_in_2_c1

theorem returnMap_single_cycle_c1 : Shared.IsSingleCycleMap ((schedule m).returnMap 1) := by
  let S₀ : Equiv.Perm (Root m) :=
    Equiv.ofBijective _ (Layers.pre_bijective _ (stageLayer_bijective (1 : Fin 5) 3) m)
  let P : Equiv.Perm (Root m) :=
    Equiv.ofBijective _ (Layers.pre_bijective _ (stageLayer_bijective (1 : Fin 5) 3) 2)
  have hPeq : ⇑P = Layers.pre (stageLayer 1 3) 2 := rfl
  have hS₀eq : ⇑S₀ = Layers.pre (stageLayer 1 3) m := rfl
  have hret : (schedule m).returnMap 1 =
      Layers.pre (stageLayer 1 3) m ∘ (P.symm ∘ Jplane (dirs 0) ∘ P) := by
    rw [returnMap_eq_pre]
    exact Layers.pre_change (stageLayer 1 3) (actual1 m) 2 m (by omega) (Jplane (dirs 0))
      (fun s hs hsm => actual1_eq h6 hm s hsm hs) (actual1_two h6 hm) P hPeq
  let S : Equiv.Perm (Root m) := (P.symm.trans S₀).trans P
  have hS : ∀ x, Chronological.orbitSet S x = coset (colSpan (castM (m := m) Hz_c1p3next)) x :=
    orbitSet_conj_coset S₀ P _ (by simpa [hS₀eq] using orbits_c1_final h6 hm) _
      (by simpa [hPeq] using prefix_c1 h6 hm)
  have hSJ := terminal_c1 h6 hm S hS
  refine Shared.single_cycle_of_equiv_conj P.symm ((schedule m).returnMap 1)
    (fun x => S (Jplane (dirs 0) x)) hSJ ?_
  intro x
  rw [hret]
  simp only [Function.comp, Equiv.symm_symm, Equiv.apply_symm_apply]
  rfl

end colour1

end D5
end TorusEven
