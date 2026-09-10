-- STATUS: main-path (Proposition prop:d5-preterminal: return orbits are the cosets of the chain)
import TorusEven.D5.LayerEval
import TorusEven.D5.Stage

/-!
# Preterminal degree-five factors (manuscript Proposition `prop:d5-preterminal`)

For each colour the layers are modified one height at a time.  Stage `k` enables the rows of
heights `< k`.  Starting from the pure translations (orbits: cosets of `⟨λ_c⟩`), each stage
applies the chronological splice, so the orbits of the stage-`k` return are the cosets of the
`k`-th column span of the colour's chain.  The final stages are the preterminal layers.
-/

namespace TorusEven
namespace D5

open Cert D5Data Chronological

variable {m : ℕ} [NeZero m]

/-- The correction of colour `c` at height `t` (zero if there is no row). -/
def corr (c : Fin 5) (t : ℕ) (x : Root m) : Root m :=
  match rowOf c t with
  | some (P, e) => if maskP P x then castV e else 0
  | none => 0

/-- Stage-`k` layer of colour `c` at height `t`: rows of height `< k` are enabled. -/
def stageLayer (c : Fin 5) (k t : ℕ) (x : Root m) : Root m :=
  x + uvec (neut c t) + (if t < k then corr c t x else 0)

theorem preLayer_eq_corr (c : Fin 5) (t : ℕ) (x : Root m) :
    preLayer c t x = x + uvec (neut c t) + corr c t x := rfl

theorem preLayer_eq_stage (c : Fin 5) (t : ℕ) : preLayer (m := m) c t = stageLayer c 3 t := by
  funext x
  rw [preLayer_eq_corr]
  unfold stageLayer
  by_cases ht : t < 3
  · simp [ht]
  · have hrow : rowOf c t = none := by
      fin_cases c <;> (rcases t with _ | _ | _ | t <;> simp [rowOf] <;> omega)
    simp [ht, corr, hrow]

theorem corr_eq_piecewise (c : Fin 5) (t : ℕ) (P : Fin 5) (e : Fin 4 → ℤ)
    (hrow : rowOf c t = some (P, e)) (x : Root m) :
    x + corr c t x = piecewiseAdd (WP m P) (zP P) (castV e) x := by
  rw [piecewiseAdd_WP]
  unfold corr
  rw [hrow]
  by_cases h : maskP P x <;> simp [h]

/-- Every row displacement lies in its cylinder's direction module. -/
theorem rowOf_mem_WP (c : Fin 5) (t : ℕ) (P : Fin 5) (e : Fin 4 → ℤ)
    (hrow : rowOf c t = some (P, e)) : castV (m := m) e ∈ WP m P := by
  fin_cases c <;> (rcases t with _ | _ | _ | t <;> simp [rowOf] at hrow) <;>
    obtain ⟨rfl, rfl⟩ := hrow
  · exact e_mem_c0p0
  · exact e_mem_c0p2
  · exact e_mem_c0p4
  · exact e_mem_c1p0
  · exact e_mem_c1p3
  · exact e_mem_c2p0
  · exact e_mem_c2p3
  · exact e_mem_c2p4
  · exact e_mem_c3p1
  · exact e_mem_c3p2
  · exact e_mem_c4p1
  · exact e_mem_c4p2

theorem stageLayer_succ_ne (c : Fin 5) (k : ℕ) :
    ∀ s, s ≠ k → stageLayer (m := m) c (k + 1) s = stageLayer c k s := by
  intro s hs
  funext x
  unfold stageLayer
  have : (s < k + 1) ↔ (s < k) := by omega
  simp only [this]

theorem stageLayer_succ_self (c : Fin 5) (k : ℕ) (P : Fin 5) (e : Fin 4 → ℤ)
    (hrow : rowOf c k = some (P, e)) :
    stageLayer (m := m) c (k + 1) k = stageLayer c k k ∘ piecewiseAdd (WP m P) (zP P) (castV e) := by
  funext x
  simp only [stageLayer, Function.comp, lt_irrefl, if_false, add_zero, Nat.lt_succ_self, if_true]
  rw [← corr_eq_piecewise c k P e hrow]
  abel

theorem stageLayer_bijective (c : Fin 5) (k : ℕ) :
    ∀ t, Function.Bijective (stageLayer (m := m) c k t) := by
  intro t
  by_cases ht : t < k
  · rcases hrow : rowOf c t with _ | ⟨P, e⟩
    · have : stageLayer (m := m) c k t = fun x => x + uvec (neut c t) := by
        funext x
        simp [stageLayer, ht, corr, hrow]
      rw [this]
      exact (Equiv.addRight _).bijective
    · have : stageLayer (m := m) c k t =
          (fun x => x + uvec (neut c t)) ∘ piecewiseAdd (WP m P) (zP P) (castV e) := by
        funext x
        simp only [stageLayer, ht, if_true, Function.comp]
        rw [← corr_eq_piecewise c t P e hrow]
        abel
      rw [this]
      exact (Equiv.addRight _).bijective.comp
        (piecewiseAdd_bijective _ _ (rowOf_mem_WP c t P e hrow) _)
  · have : stageLayer (m := m) c k t = fun x => x + uvec (neut c t) := by
      funext x
      simp [stageLayer, ht]
    rw [this]
    exact (Equiv.addRight _).bijective


/-! ### Prefixes and the base translation -/

theorem prefix_stage (c : Fin 5) (k : ℕ) (H : AddSubgroup (Root m))
    (hH : ∀ s, s < k → ∀ P e, rowOf c s = some (P, e) → castV e ∈ H) :
    ∀ t x, Layers.pre (stageLayer c k) t x - x - (∑ s ∈ Finset.range t, uvec (neut c s)) ∈ H := by
  apply Stage.prefix_mem
  intro s x
  simp only [stageLayer]
  have h : x + uvec (neut c s) + (if s < k then corr c s x else 0) - x - uvec (neut c s) =
      (if s < k then corr c s x else 0) := by abel
  rw [h]
  split_ifs with hs
  · unfold corr
    rcases hrow : rowOf c s with _ | ⟨P, e⟩
    · exact H.zero_mem
    · dsimp only
      split_ifs
      · exact hH s hs P e hrow
      · exact H.zero_mem
  · exact H.zero_mem

def lamOf : Fin 5 → (Fin 4 → ℤ)
  | 0 => lam_c0
  | 1 => lam_c1
  | 2 => lam_c2
  | 3 => lam_c3
  | 4 => lam_c4

def ones : Root m := fun _ => 1

theorem sum_first_five (c : Fin 5) : ∑ s ∈ Finset.range 5, uvec (neut c s) = (ones : Root m) := by
  fin_cases c <;> simp +decide [Finset.sum_range_succ, neut] <;> ext i <;> fin_cases i <;>
    simp +decide [uvec, ones]

theorem neut_of_ge (c : Fin 5) (s : ℕ) (hs : 5 ≤ s) : neut c s = c := by
  simp [neut]
  omega

theorem sum_uvec_neut (hm : 6 ≤ m) (c : Fin 5) :
    ∑ s ∈ Finset.range m, uvec (neut c s) = castV (m := m) (lamOf c) := by
  have hr : Finset.range m = Finset.range (5 + (m - 5)) := by rw [Nat.add_sub_of_le (by omega)]
  rw [hr, Finset.sum_range_add, sum_first_five]
  have h2 : ∑ s ∈ Finset.range (m - 5), uvec (neut c (5 + s)) = (m - 5) • (uvec c : Root m) := by
    rw [Finset.sum_congr rfl (fun s _ => by rw [neut_of_ge c (5 + s) (by omega)])]
    simp
  rw [h2]
  have h5 : ((m - 5 : ℕ) : ZMod m) = -5 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  ext i
  fin_cases c <;> fin_cases i <;> simp [ones, uvec, castV, lamOf, lam_c0, lam_c1, lam_c2, lam_c3,
    lam_c4, nsmul_eq_mul, h5] <;> norm_num

theorem base_orbits (hm : 6 ≤ m) (c : Fin 5) (x : Root m) :
    Chronological.orbitSet (Layers.pre (stageLayer c 0) m) x =
      coset (AddSubgroup.zmultiples (castV (lamOf c))) x := by
  have hpre : Layers.pre (stageLayer (m := m) c 0) m = fun x => x + castV (m := m) (lamOf c) := by
    funext x
    have := Stage.prefix_mem (stageLayer c 0) (fun s => uvec (neut c s)) ⊥
      (by intro s x; simp [stageLayer]) m x
    rw [AddSubgroup.mem_bot, sub_eq_zero, sub_eq_iff_eq_add, sum_uvec_neut hm c] at this
    rw [this]
    abel
  rw [hpre]
  exact Stage.orbitSet_translation _ x

/-! ### The stages, colour by colour -/

theorem mem_c0p0_in_1_c0 : castV (m := m) e_c0p0 ∈ colSpan (castM Hz_c0p0next) := by
  rw [chain_c0p0]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

theorem mem_c0p0_in_2_c0 : castV (m := m) e_c0p0 ∈ colSpan (castM Hz_c0p2next) := by
  rw [chain_c0p2]
  apply AddSubgroup.mem_sup_left
  rw [chain_c0p0]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

theorem mem_c0p2_in_2_c0 : castV (m := m) e_c0p2 ∈ colSpan (castM Hz_c0p2next) := by
  rw [chain_c0p2]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

theorem mem_c0p0_in_3_c0 : castV (m := m) e_c0p0 ∈ colSpan (castM Hz_c0p4next) := by
  rw [chain_c0p4]
  apply AddSubgroup.mem_sup_left
  rw [chain_c0p2]
  apply AddSubgroup.mem_sup_left
  rw [chain_c0p0]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

theorem mem_c0p2_in_3_c0 : castV (m := m) e_c0p2 ∈ colSpan (castM Hz_c0p4next) := by
  rw [chain_c0p4]
  apply AddSubgroup.mem_sup_left
  rw [chain_c0p2]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

theorem mem_c0p4_in_3_c0 : castV (m := m) e_c0p4 ∈ colSpan (castM Hz_c0p4next) := by
  rw [chain_c0p4]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

theorem orbits_c0_0 (hm : 6 ≤ m) :
    ∀ x, Chronological.orbitSet (Layers.pre (stageLayer (0 : Fin 5) 0) m) x =
      coset (colSpan (castM (m := m) Hz_c0base)) x := by
  intro x
  rw [base_c0]
  exact base_orbits hm 0 x

theorem orbits_c0_1 (hm : 6 ≤ m) :
    ∀ x, Chronological.orbitSet (Layers.pre (stageLayer (0 : Fin 5) 1) m) x =
      coset (colSpan (castM (m := m) Hz_c0p0next)) x := by
  intro x
  rw [chain_c0p0]
  refine Stage.step (stageLayer 0 0) (stageLayer 0 1) (stageLayer_bijective _ _) 0
    (by omega) (colSpan (castM (m := m) Hz_c0base)) (WP m 0) isCompl_c0p0 (orbits_c0_0 hm)
    (∑ s ∈ Finset.range 0, uvec (neut 0 s)) (prefix_stage 0 0 _ ?_ 0)
    (zP 0) (castV e_c0p0) e_mem_c0p0 (stageLayer_succ_ne 0 0)
    (stageLayer_succ_self 0 0 0 e_c0p0 rfl) x
  intro s hs P e hrow
  exact absurd hs (by omega)

theorem orbits_c0_2 (hm : 6 ≤ m) :
    ∀ x, Chronological.orbitSet (Layers.pre (stageLayer (0 : Fin 5) 2) m) x =
      coset (colSpan (castM (m := m) Hz_c0p2next)) x := by
  intro x
  rw [chain_c0p2]
  refine Stage.step (stageLayer 0 1) (stageLayer 0 2) (stageLayer_bijective _ _) 1
    (by omega) (colSpan (castM (m := m) Hz_c0p0next)) (WP m 2) isCompl_c0p2 (orbits_c0_1 hm)
    (∑ s ∈ Finset.range 1, uvec (neut 0 s)) (prefix_stage 0 1 _ ?_ 1)
    (zP 2) (castV e_c0p2) e_mem_c0p2 (stageLayer_succ_ne 0 1)
    (stageLayer_succ_self 0 1 2 e_c0p2 rfl) x
  intro s hs P e hrow
  interval_cases s
  simp [rowOf] at hrow
  obtain ⟨rfl, rfl⟩ := hrow
  exact mem_c0p0_in_1_c0

theorem orbits_c0_3 (hm : 6 ≤ m) :
    ∀ x, Chronological.orbitSet (Layers.pre (stageLayer (0 : Fin 5) 3) m) x =
      coset (colSpan (castM (m := m) Hz_c0p4next)) x := by
  intro x
  rw [chain_c0p4]
  refine Stage.step (stageLayer 0 2) (stageLayer 0 3) (stageLayer_bijective _ _) 2
    (by omega) (colSpan (castM (m := m) Hz_c0p2next)) (WP m 4) isCompl_c0p4 (orbits_c0_2 hm)
    (∑ s ∈ Finset.range 2, uvec (neut 0 s)) (prefix_stage 0 2 _ ?_ 2)
    (zP 4) (castV e_c0p4) e_mem_c0p4 (stageLayer_succ_ne 0 2)
    (stageLayer_succ_self 0 2 4 e_c0p4 rfl) x
  intro s hs P e hrow
  interval_cases s <;> simp [rowOf] at hrow <;> obtain ⟨rfl, rfl⟩ := hrow
  · exact mem_c0p0_in_2_c0
  · exact mem_c0p2_in_2_c0

theorem mem_c1p0_in_1_c1 : castV (m := m) e_c1p0 ∈ colSpan (castM Hz_c1p0next) := by
  rw [chain_c1p0]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

theorem mem_c1p0_in_2_c1 : castV (m := m) e_c1p0 ∈ colSpan (castM Hz_c1p3next) := by
  rw [chain_c1p3]
  apply AddSubgroup.mem_sup_left
  rw [chain_c1p0]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

theorem mem_c1p3_in_2_c1 : castV (m := m) e_c1p3 ∈ colSpan (castM Hz_c1p3next) := by
  rw [chain_c1p3]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

theorem orbits_c1_0 (hm : 6 ≤ m) :
    ∀ x, Chronological.orbitSet (Layers.pre (stageLayer (1 : Fin 5) 0) m) x =
      coset (colSpan (castM (m := m) Hz_c1base)) x := by
  intro x
  rw [base_c1]
  exact base_orbits hm 1 x

theorem orbits_c1_1 (hm : 6 ≤ m) :
    ∀ x, Chronological.orbitSet (Layers.pre (stageLayer (1 : Fin 5) 1) m) x =
      coset (colSpan (castM (m := m) Hz_c1p0next)) x := by
  intro x
  rw [chain_c1p0]
  refine Stage.step (stageLayer 1 0) (stageLayer 1 1) (stageLayer_bijective _ _) 0
    (by omega) (colSpan (castM (m := m) Hz_c1base)) (WP m 0) isCompl_c1p0 (orbits_c1_0 hm)
    (∑ s ∈ Finset.range 0, uvec (neut 1 s)) (prefix_stage 1 0 _ ?_ 0)
    (zP 0) (castV e_c1p0) e_mem_c1p0 (stageLayer_succ_ne 1 0)
    (stageLayer_succ_self 1 0 0 e_c1p0 rfl) x
  intro s hs P e hrow
  exact absurd hs (by omega)

theorem orbits_c1_2 (hm : 6 ≤ m) :
    ∀ x, Chronological.orbitSet (Layers.pre (stageLayer (1 : Fin 5) 2) m) x =
      coset (colSpan (castM (m := m) Hz_c1p3next)) x := by
  intro x
  rw [chain_c1p3]
  refine Stage.step (stageLayer 1 1) (stageLayer 1 2) (stageLayer_bijective _ _) 1
    (by omega) (colSpan (castM (m := m) Hz_c1p0next)) (WP m 3) isCompl_c1p3 (orbits_c1_1 hm)
    (∑ s ∈ Finset.range 1, uvec (neut 1 s)) (prefix_stage 1 1 _ ?_ 1)
    (zP 3) (castV e_c1p3) e_mem_c1p3 (stageLayer_succ_ne 1 1)
    (stageLayer_succ_self 1 1 3 e_c1p3 rfl) x
  intro s hs P e hrow
  interval_cases s
  simp [rowOf] at hrow
  obtain ⟨rfl, rfl⟩ := hrow
  exact mem_c1p0_in_1_c1

theorem mem_c2p0_in_1_c2 : castV (m := m) e_c2p0 ∈ colSpan (castM Hz_c2p0next) := by
  rw [chain_c2p0]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

theorem mem_c2p0_in_2_c2 : castV (m := m) e_c2p0 ∈ colSpan (castM Hz_c2p3next) := by
  rw [chain_c2p3]
  apply AddSubgroup.mem_sup_left
  rw [chain_c2p0]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

theorem mem_c2p3_in_2_c2 : castV (m := m) e_c2p3 ∈ colSpan (castM Hz_c2p3next) := by
  rw [chain_c2p3]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

theorem mem_c2p0_in_3_c2 : castV (m := m) e_c2p0 ∈ colSpan (castM Hz_c2p4next) := by
  rw [chain_c2p4]
  apply AddSubgroup.mem_sup_left
  rw [chain_c2p3]
  apply AddSubgroup.mem_sup_left
  rw [chain_c2p0]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

theorem mem_c2p3_in_3_c2 : castV (m := m) e_c2p3 ∈ colSpan (castM Hz_c2p4next) := by
  rw [chain_c2p4]
  apply AddSubgroup.mem_sup_left
  rw [chain_c2p3]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

theorem mem_c2p4_in_3_c2 : castV (m := m) e_c2p4 ∈ colSpan (castM Hz_c2p4next) := by
  rw [chain_c2p4]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

theorem orbits_c2_0 (hm : 6 ≤ m) :
    ∀ x, Chronological.orbitSet (Layers.pre (stageLayer (2 : Fin 5) 0) m) x =
      coset (colSpan (castM (m := m) Hz_c2base)) x := by
  intro x
  rw [base_c2]
  exact base_orbits hm 2 x

theorem orbits_c2_1 (hm : 6 ≤ m) :
    ∀ x, Chronological.orbitSet (Layers.pre (stageLayer (2 : Fin 5) 1) m) x =
      coset (colSpan (castM (m := m) Hz_c2p0next)) x := by
  intro x
  rw [chain_c2p0]
  refine Stage.step (stageLayer 2 0) (stageLayer 2 1) (stageLayer_bijective _ _) 0
    (by omega) (colSpan (castM (m := m) Hz_c2base)) (WP m 0) isCompl_c2p0 (orbits_c2_0 hm)
    (∑ s ∈ Finset.range 0, uvec (neut 2 s)) (prefix_stage 2 0 _ ?_ 0)
    (zP 0) (castV e_c2p0) e_mem_c2p0 (stageLayer_succ_ne 2 0)
    (stageLayer_succ_self 2 0 0 e_c2p0 rfl) x
  intro s hs P e hrow
  exact absurd hs (by omega)

theorem orbits_c2_2 (hm : 6 ≤ m) :
    ∀ x, Chronological.orbitSet (Layers.pre (stageLayer (2 : Fin 5) 2) m) x =
      coset (colSpan (castM (m := m) Hz_c2p3next)) x := by
  intro x
  rw [chain_c2p3]
  refine Stage.step (stageLayer 2 1) (stageLayer 2 2) (stageLayer_bijective _ _) 1
    (by omega) (colSpan (castM (m := m) Hz_c2p0next)) (WP m 3) isCompl_c2p3 (orbits_c2_1 hm)
    (∑ s ∈ Finset.range 1, uvec (neut 2 s)) (prefix_stage 2 1 _ ?_ 1)
    (zP 3) (castV e_c2p3) e_mem_c2p3 (stageLayer_succ_ne 2 1)
    (stageLayer_succ_self 2 1 3 e_c2p3 rfl) x
  intro s hs P e hrow
  interval_cases s
  simp [rowOf] at hrow
  obtain ⟨rfl, rfl⟩ := hrow
  exact mem_c2p0_in_1_c2

theorem orbits_c2_3 (hm : 6 ≤ m) :
    ∀ x, Chronological.orbitSet (Layers.pre (stageLayer (2 : Fin 5) 3) m) x =
      coset (colSpan (castM (m := m) Hz_c2p4next)) x := by
  intro x
  rw [chain_c2p4]
  refine Stage.step (stageLayer 2 2) (stageLayer 2 3) (stageLayer_bijective _ _) 2
    (by omega) (colSpan (castM (m := m) Hz_c2p3next)) (WP m 4) isCompl_c2p4 (orbits_c2_2 hm)
    (∑ s ∈ Finset.range 2, uvec (neut 2 s)) (prefix_stage 2 2 _ ?_ 2)
    (zP 4) (castV e_c2p4) e_mem_c2p4 (stageLayer_succ_ne 2 2)
    (stageLayer_succ_self 2 2 4 e_c2p4 rfl) x
  intro s hs P e hrow
  interval_cases s <;> simp [rowOf] at hrow <;> obtain ⟨rfl, rfl⟩ := hrow
  · exact mem_c2p0_in_2_c2
  · exact mem_c2p3_in_2_c2

theorem mem_c3p1_in_1_c3 : castV (m := m) e_c3p1 ∈ colSpan (castM Hz_c3p1next) := by
  rw [chain_c3p1]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

theorem mem_c3p1_in_2_c3 : castV (m := m) e_c3p1 ∈ colSpan (castM Hz_c3p2next) := by
  rw [chain_c3p2]
  apply AddSubgroup.mem_sup_left
  rw [chain_c3p1]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

theorem mem_c3p2_in_2_c3 : castV (m := m) e_c3p2 ∈ colSpan (castM Hz_c3p2next) := by
  rw [chain_c3p2]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

theorem orbits_c3_0 (hm : 6 ≤ m) :
    ∀ x, Chronological.orbitSet (Layers.pre (stageLayer (3 : Fin 5) 0) m) x =
      coset (colSpan (castM (m := m) Hz_c3base)) x := by
  intro x
  rw [base_c3]
  exact base_orbits hm 3 x

theorem orbits_c3_1 (hm : 6 ≤ m) :
    ∀ x, Chronological.orbitSet (Layers.pre (stageLayer (3 : Fin 5) 1) m) x =
      coset (colSpan (castM (m := m) Hz_c3p1next)) x := by
  intro x
  rw [chain_c3p1]
  refine Stage.step (stageLayer 3 0) (stageLayer 3 1) (stageLayer_bijective _ _) 0
    (by omega) (colSpan (castM (m := m) Hz_c3base)) (WP m 1) isCompl_c3p1 (orbits_c3_0 hm)
    (∑ s ∈ Finset.range 0, uvec (neut 3 s)) (prefix_stage 3 0 _ ?_ 0)
    (zP 1) (castV e_c3p1) e_mem_c3p1 (stageLayer_succ_ne 3 0)
    (stageLayer_succ_self 3 0 1 e_c3p1 rfl) x
  intro s hs P e hrow
  exact absurd hs (by omega)

theorem orbits_c3_2 (hm : 6 ≤ m) :
    ∀ x, Chronological.orbitSet (Layers.pre (stageLayer (3 : Fin 5) 2) m) x =
      coset (colSpan (castM (m := m) Hz_c3p2next)) x := by
  intro x
  rw [chain_c3p2]
  refine Stage.step (stageLayer 3 1) (stageLayer 3 2) (stageLayer_bijective _ _) 1
    (by omega) (colSpan (castM (m := m) Hz_c3p1next)) (WP m 2) isCompl_c3p2 (orbits_c3_1 hm)
    (∑ s ∈ Finset.range 1, uvec (neut 3 s)) (prefix_stage 3 1 _ ?_ 1)
    (zP 2) (castV e_c3p2) e_mem_c3p2 (stageLayer_succ_ne 3 1)
    (stageLayer_succ_self 3 1 2 e_c3p2 rfl) x
  intro s hs P e hrow
  interval_cases s
  simp [rowOf] at hrow
  obtain ⟨rfl, rfl⟩ := hrow
  exact mem_c3p1_in_1_c3

theorem mem_c4p1_in_1_c4 : castV (m := m) e_c4p1 ∈ colSpan (castM Hz_c4p1next) := by
  rw [chain_c4p1]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

theorem mem_c4p1_in_2_c4 : castV (m := m) e_c4p1 ∈ colSpan (castM Hz_c4p2next) := by
  rw [chain_c4p2]
  apply AddSubgroup.mem_sup_left
  rw [chain_c4p1]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

theorem mem_c4p2_in_2_c4 : castV (m := m) e_c4p2 ∈ colSpan (castM Hz_c4p2next) := by
  rw [chain_c4p2]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

theorem orbits_c4_0 (hm : 6 ≤ m) :
    ∀ x, Chronological.orbitSet (Layers.pre (stageLayer (4 : Fin 5) 0) m) x =
      coset (colSpan (castM (m := m) Hz_c4base)) x := by
  intro x
  rw [base_c4]
  exact base_orbits hm 4 x

theorem orbits_c4_1 (hm : 6 ≤ m) :
    ∀ x, Chronological.orbitSet (Layers.pre (stageLayer (4 : Fin 5) 1) m) x =
      coset (colSpan (castM (m := m) Hz_c4p1next)) x := by
  intro x
  rw [chain_c4p1]
  refine Stage.step (stageLayer 4 0) (stageLayer 4 1) (stageLayer_bijective _ _) 0
    (by omega) (colSpan (castM (m := m) Hz_c4base)) (WP m 1) isCompl_c4p1 (orbits_c4_0 hm)
    (∑ s ∈ Finset.range 0, uvec (neut 4 s)) (prefix_stage 4 0 _ ?_ 0)
    (zP 1) (castV e_c4p1) e_mem_c4p1 (stageLayer_succ_ne 4 0)
    (stageLayer_succ_self 4 0 1 e_c4p1 rfl) x
  intro s hs P e hrow
  exact absurd hs (by omega)

theorem orbits_c4_2 (hm : 6 ≤ m) :
    ∀ x, Chronological.orbitSet (Layers.pre (stageLayer (4 : Fin 5) 2) m) x =
      coset (colSpan (castM (m := m) Hz_c4p2next)) x := by
  intro x
  rw [chain_c4p2]
  refine Stage.step (stageLayer 4 1) (stageLayer 4 2) (stageLayer_bijective _ _) 1
    (by omega) (colSpan (castM (m := m) Hz_c4p1next)) (WP m 2) isCompl_c4p2 (orbits_c4_1 hm)
    (∑ s ∈ Finset.range 1, uvec (neut 4 s)) (prefix_stage 4 1 _ ?_ 1)
    (zP 2) (castV e_c4p2) e_mem_c4p2 (stageLayer_succ_ne 4 1)
    (stageLayer_succ_self 4 1 2 e_c4p2 rfl) x
  intro s hs P e hrow
  interval_cases s
  simp [rowOf] at hrow
  obtain ⟨rfl, rfl⟩ := hrow
  exact mem_c4p1_in_1_c4

end D5
end TorusEven
