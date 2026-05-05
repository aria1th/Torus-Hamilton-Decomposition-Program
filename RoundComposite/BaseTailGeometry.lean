import Mathlib
import RoundComposite.ActiveHall
import Shared.TorusCayley

namespace RoundComposite
namespace Concrete
namespace BaseTail

def activeDir (b : Nat) : Fin (b + 1) :=
  Fin.last b

structure Cylinder (b m T : Nat) (packets : List (List Nat)) where
  dir : Fin (b + T) → Shared.TorusVertex (b + 1) m → Fin (b + 1)
  active_card :
    ∀ x : Shared.TorusVertex (b + 1) m,
      ((Finset.univ : Finset (Fin (b + T))).filter
        (fun c => dir c x = activeDir b)).card = T

namespace Cylinder

def active {b m T : Nat} {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets)
    (x : Shared.TorusVertex (b + 1) m) : Finset (Fin (b + T)) :=
  (Finset.univ : Finset (Fin (b + T))).filter
    (fun c => Cyl.dir c x = activeDir b)

noncomputable def incidence {b m T : Nat} [NeZero m]
    {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets) :
    ActiveHall.Incidence T
      (Shared.TorusVertex (b + 1) m) (Fin (b + T)) where
  active := Cyl.active
  active_card := by
    intro x
    exact Cyl.active_card x

def step {b m T : Nat} {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets)
    (c : Fin (b + T)) :
    Shared.TorusVertex (b + 1) m → Shared.TorusVertex (b + 1) m :=
  fun x => x + Shared.torusBasis (b + 1) m (Cyl.dir c x)

end Cylinder

def ordinaryExpandedDir {b T : Nat}
    (i : Fin (b + 1)) (hi : i ≠ activeDir b) : Fin (b + T) :=
  ⟨i.val, by
    have hlt : i.val < b := by
      by_contra hnot
      have hv : i.val = b := by omega
      exact hi (by
        apply Fin.ext
        simp [activeDir, hv])
    omega⟩

def tailExpandedDir (b : Nat) {T : Nat} (σ : Fin T) : Fin (b + T) :=
  ⟨b + σ.val, by omega⟩

def ordinaryBaseDirOfExpandedDir {b T : Nat}
    (i : Fin (b + T)) (hi : i.val < b) : Fin (b + 1) :=
  ⟨i.val, by omega⟩

def tailSymbolOfExpandedDir {b T : Nat}
    (i : Fin (b + T)) (hi : b ≤ i.val) : Fin T :=
  ⟨i.val - b, by omega⟩

theorem ordinaryBaseDirOfExpandedDir_ne_active {b T : Nat}
    (i : Fin (b + T)) (hi : i.val < b) :
    ordinaryBaseDirOfExpandedDir i hi ≠ activeDir b := by
  intro h
  have hv := congrArg Fin.val h
  simp [ordinaryBaseDirOfExpandedDir, activeDir] at hv
  omega

theorem ordinaryExpandedDir_val_lt {b T : Nat}
    (i : Fin (b + 1)) (hi : i ≠ activeDir b) :
    (ordinaryExpandedDir (T := T) i hi).val < b := by
  have hval : (ordinaryExpandedDir (T := T) i hi).val = i.val := rfl
  by_contra hnot
  rw [hval] at hnot
  have hv : i.val = b := by omega
  exact hi (by
    apply Fin.ext
    simp [activeDir, hv])

theorem ordinaryExpandedDir_of_ordinaryBaseDir {b T : Nat}
    (i : Fin (b + T)) (hi : i.val < b) :
    ordinaryExpandedDir
        (ordinaryBaseDirOfExpandedDir i hi)
        (ordinaryBaseDirOfExpandedDir_ne_active i hi) = i := by
  apply Fin.ext
  simp [ordinaryExpandedDir, ordinaryBaseDirOfExpandedDir]

theorem tailExpandedDir_val_ge (b : Nat) {T : Nat} (σ : Fin T) :
    b ≤ (tailExpandedDir b σ).val := by
  simp [tailExpandedDir]

theorem tailExpandedDir_of_tailSymbol {b T : Nat}
    (i : Fin (b + T)) (hi : b ≤ i.val) :
    tailExpandedDir b (tailSymbolOfExpandedDir i hi) = i := by
  apply Fin.ext
  simp [tailExpandedDir, tailSymbolOfExpandedDir]
  omega

theorem tailExpandedDir_injective {b T : Nat} :
    Function.Injective (tailExpandedDir b : Fin T → Fin (b + T)) := by
  intro σ τ h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp [tailExpandedDir] at hv
  omega

theorem ordinaryExpandedDir_ne_tailExpandedDir {b T : Nat}
    (i : Fin (b + 1)) (hi : i ≠ activeDir b) (σ : Fin T) :
    ordinaryExpandedDir (T := T) i hi ≠ tailExpandedDir b σ := by
  intro h
  have hlt := ordinaryExpandedDir_val_lt (T := T) i hi
  have hge := tailExpandedDir_val_ge b σ
  rw [h] at hlt
  omega

def collapseVertex (b m T : Nat)
    (x : Shared.TorusVertex (b + T) m) :
    Shared.TorusVertex (b + 1) m :=
  fun i =>
    if hi : i.val < b then
      x ⟨i.val, by omega⟩
    else
      ∑ σ : Fin T, x (tailExpandedDir b σ)

structure IsCylinder {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets) : Prop where
  ordinary_unique :
    ∀ x : Shared.TorusVertex (b + 1) m,
      ∀ i : Fin (b + 1), i ≠ activeDir b →
        ∃! c : Fin (b + T), Cyl.dir c x = i
  color_hamiltonian :
    ∀ c : Fin (b + T), Shared.IsSingleCycleMap (Cyl.step c)
  active_degree_mod :
    ∀ c : Fin (b + T),
      (((Cyl.incidence).colorDegree c : Nat) : ZMod m) = 0

structure ActiveBlockData {b m T : Nat} [NeZero m]
    {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets) where
  activeBlock : Fin (b + T) → Nat
  activeBlock_pos : ∀ c : Fin (b + T), 0 < activeBlock c
  activeBlock_lt : ∀ c : Fin (b + T), activeBlock c < m
  activeBlock_coprime : ∀ c : Fin (b + T), Nat.Coprime (activeBlock c) m
  active_degree_eq :
    ∀ c : Fin (b + T),
      (Cyl.incidence).colorDegree c = (m - activeBlock c) * m ^ b

structure MixedExpansionData {b m T : Nat} [NeZero m]
    {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets) where
  mixed_lower :
    ∀ U : Finset (Fin (b + T)),
      U.Nonempty → U ≠ Finset.univ →
        m ^ b ≤ (Cyl.incidence).mixedCount U

namespace MixedExpansionData

theorem mixed_lower_compl
    {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : MixedExpansionData Cyl) {U : Finset (Fin (b + T))}
    (hUne : U.Nonempty) (hUuniv : U ≠ Finset.univ) :
    m ^ b ≤ (Cyl.incidence).mixedCount Uᶜ := by
  classical
  have hcomp_ne : Uᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    exact hUuniv ((Finset.compl_eq_empty_iff U).mp hEmpty)
  have hcomp_univ : Uᶜ ≠ (Finset.univ : Finset (Fin (b + T))) := by
    intro hUniv
    exact hUne.ne_empty ((Finset.compl_eq_univ_iff U).mp hUniv)
  exact D.mixed_lower Uᶜ hcomp_ne hcomp_univ

theorem slack_error_le_mixedCount_mul_proper_min
    {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : MixedExpansionData Cyl) {U : Finset (Fin (b + T))}
    (hUne : U.Nonempty) (hUuniv : U ≠ Finset.univ)
    (hTpos : 0 < T) (hSlack : m ^ b > m * (b + T) * T)
    (S : Finset (Fin T)) :
    m * (b + T) * min S.card (T - S.card)
      ≤ (Cyl.incidence).mixedCount U * min S.card (T - S.card) := by
  have hbaseScale : m * (b + T) ≤ m * (b + T) * T := by
    exact Nat.le_mul_of_pos_right (m * (b + T)) hTpos
  have hbaseLtPow : m * (b + T) < m ^ b :=
    hbaseScale.trans_lt hSlack
  have hbaseLeMixed : m * (b + T) ≤ (Cyl.incidence).mixedCount U :=
    Nat.le_of_lt (hbaseLtPow.trans_le (D.mixed_lower U hUne hUuniv))
  simpa [Nat.mul_assoc] using
    Nat.mul_le_mul_right (min S.card (T - S.card)) hbaseLeMixed

theorem slack_error_le_mixedCount_compl_mul_proper_min
    {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : MixedExpansionData Cyl) {U : Finset (Fin (b + T))}
    (hUne : U.Nonempty) (hUuniv : U ≠ Finset.univ)
    (hTpos : 0 < T) (hSlack : m ^ b > m * (b + T) * T)
    (S : Finset (Fin T)) :
    m * (b + T) * min S.card (T - S.card)
      ≤ (Cyl.incidence).mixedCount Uᶜ * min S.card (T - S.card) := by
  have hbaseScale : m * (b + T) ≤ m * (b + T) * T := by
    exact Nat.le_mul_of_pos_right (m * (b + T)) hTpos
  have hbaseLtPow : m * (b + T) < m ^ b :=
    hbaseScale.trans_lt hSlack
  have hbaseLeMixed : m * (b + T) ≤ (Cyl.incidence).mixedCount Uᶜ :=
    Nat.le_of_lt (hbaseLtPow.trans_le (D.mixed_lower_compl hUne hUuniv))
  simpa [Nat.mul_assoc] using
    Nat.mul_le_mul_right (min S.card (T - S.card)) hbaseLeMixed

theorem hallCuts_of_scaled_error_le_slack
    {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : MixedExpansionData Cyl) (hTpos : 0 < T)
    (hSlack : m ^ b > m * (b + T) * T)
    (M : ActiveHall.CountMatrix Cyl.incidence)
    (hScaled :
      ∀ U : Finset (Fin (b + T)), ∀ S : Finset (Fin T),
        U.Nonempty → U ≠ Finset.univ →
        S.Nonempty → S ≠ Finset.univ →
          T * M.cutMass U S ≤
            S.card * (∑ c ∈ U, (Cyl.incidence).colorDegree c) +
              m * (b + T) * min S.card (T - S.card)) :
    M.HallCuts := by
  apply M.hallCuts_of_nontrivial_scaled_bary_error_le_mixed hTpos
  intro U S hUne hUuniv hSne hSuniv
  exact
    (hScaled U S hUne hUuniv hSne hSuniv).trans
      (Nat.add_le_add_left
        (D.slack_error_le_mixedCount_mul_proper_min
          hUne hUuniv hTpos hSlack S)
        (S.card * (∑ c ∈ U, (Cyl.incidence).colorDegree c)))

theorem feasibleWithResidues_of_scaled_error_le_slack
    {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : MixedExpansionData Cyl) (hTpos : 0 < T)
    (hSlack : m ^ b > m * (b + T) * T)
    {R : ActiveHall.ResidueSpec m T (Fin (b + T))}
    (M : ActiveHall.CountMatrix Cyl.incidence)
    (hResidues : M.HasResidues R)
    (hScaled :
      ∀ U : Finset (Fin (b + T)), ∀ S : Finset (Fin T),
        U.Nonempty → U ≠ Finset.univ →
        S.Nonempty → S ≠ Finset.univ →
          T * M.cutMass U S ≤
            S.card * (∑ c ∈ U, (Cyl.incidence).colorDegree c) +
              m * (b + T) * min S.card (T - S.card)) :
    ActiveHall.FeasibleWithResidues Cyl.incidence R :=
  ⟨M, D.hallCuts_of_scaled_error_le_slack hTpos hSlack M hScaled,
    hResidues⟩

end MixedExpansionData

namespace ActiveBlockData

theorem active_complement_pos {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (c : Fin (b + T)) :
    0 < m - (D.activeBlock c) := by
  exact Nat.sub_pos_of_lt (D.activeBlock_lt c)

theorem activeBlock_isUnit {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (c : Fin (b + T)) :
    IsUnit ((D.activeBlock c : Nat) : ZMod m) :=
  (ZMod.isUnit_iff_coprime (D.activeBlock c) m).2
    (D.activeBlock_coprime c)

theorem active_complement_coprime {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (c : Fin (b + T)) :
    Nat.Coprime (m - (D.activeBlock c)) m :=
  (Nat.coprime_self_sub_left (Nat.le_of_lt (D.activeBlock_lt c))).2
    (D.activeBlock_coprime c)

theorem active_complement_isUnit {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (c : Fin (b + T)) :
    IsUnit (((m - (D.activeBlock c)) : Nat) : ZMod m) :=
  (ZMod.isUnit_iff_coprime (m - (D.activeBlock c)) m).2
    (D.active_complement_coprime c)

theorem active_degree_mod {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (hb : 0 < b) (c : Fin (b + T)) :
    (((Cyl.incidence).colorDegree c : Nat) : ZMod m) = 0 := by
  rw [D.active_degree_eq c]
  exact ActiveHall.zmod_natCast_mul_pow_eq_zero_of_pos hb

theorem active_degree_lower_bound {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (c : Fin (b + T)) :
    m ^ b ≤ (Cyl.incidence).colorDegree c := by
  rw [D.active_degree_eq c]
  have hfactor : 1 ≤ m - (D.activeBlock c) := by
    exact D.active_complement_pos c
  simpa using Nat.mul_le_mul_right (m ^ b) hfactor

theorem active_degree_upper_bound {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (c : Fin (b + T)) :
    (Cyl.incidence).colorDegree c ≤ (m - 1) * m ^ b := by
  rw [D.active_degree_eq c]
  have hfactor : m - (D.activeBlock c) ≤ m - 1 := by
    have hpos := D.activeBlock_pos c
    omega
  exact Nat.mul_le_mul_right (m ^ b) hfactor

theorem active_degree_pos {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (c : Fin (b + T)) :
    0 < (Cyl.incidence).colorDegree c := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hpow : 0 < m ^ b := pow_pos hmpos b
  exact lt_of_lt_of_le hpow (D.active_degree_lower_bound c)

theorem active_degree_dvd_modulus {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (hb : 0 < b) (c : Fin (b + T)) :
    m ∣ (Cyl.incidence).colorDegree c :=
  (ZMod.natCast_eq_zero_iff ((Cyl.incidence).colorDegree c) m).mp
    (D.active_degree_mod hb c)

theorem modulus_le_active_degree {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (hb : 0 < b) (c : Fin (b + T)) :
    m ≤ (Cyl.incidence).colorDegree c :=
  Nat.le_of_dvd (D.active_degree_pos c)
    (D.active_degree_dvd_modulus hb c)

theorem sum_colorDegree_lower_bound {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (U : Finset (Fin (b + T))) :
    U.card * m ^ b ≤
      ∑ c ∈ U, (Cyl.incidence).colorDegree c := by
  have hsum :
      (∑ c ∈ U, m ^ b) ≤
        ∑ c ∈ U, (Cyl.incidence).colorDegree c := by
    exact Finset.sum_le_sum (fun c _hc => D.active_degree_lower_bound c)
  simpa [Finset.sum_const, nsmul_eq_mul] using hsum

theorem sum_colorDegree_nonempty_lower_bound {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) {U : Finset (Fin (b + T))}
    (hU : U.Nonempty) :
    m ^ b ≤ ∑ c ∈ U, (Cyl.incidence).colorDegree c := by
  have hcard : 1 ≤ U.card := hU.card_pos
  have hmul : m ^ b ≤ U.card * m ^ b := by
    simpa using Nat.mul_le_mul_right (m ^ b) hcard
  exact hmul.trans (D.sum_colorDegree_lower_bound U)

theorem sum_colorDegree_compl_lower_bound {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) {U : Finset (Fin (b + T))}
    (hU : U ≠ Finset.univ) :
    m ^ b ≤
      ∑ c ∈ Uᶜ, (Cyl.incidence).colorDegree c := by
  classical
  have hcomp : Uᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    exact hU ((Finset.compl_eq_empty_iff U).mp hEmpty)
  exact D.sum_colorDegree_nonempty_lower_bound hcomp

theorem slack_error_lt_sum_colorDegree_nonempty {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) {U : Finset (Fin (b + T))}
    (hU : U.Nonempty) (hSlack : m ^ b > m * (b + T) * T)
    {k : Nat} (hk : k ≤ T) :
    m * (b + T) * k <
      ∑ c ∈ U, (Cyl.incidence).colorDegree c := by
  have hscale : m * (b + T) * k ≤ m * (b + T) * T := by
    exact Nat.mul_le_mul_left (m * (b + T)) hk
  have hlt_pow : m * (b + T) * k < m ^ b :=
    lt_of_le_of_lt hscale hSlack
  exact hlt_pow.trans_le (D.sum_colorDegree_nonempty_lower_bound hU)

theorem slack_error_lt_sum_colorDegree_compl {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) {U : Finset (Fin (b + T))}
    (hU : U ≠ Finset.univ) (hSlack : m ^ b > m * (b + T) * T)
    {k : Nat} (hk : k ≤ T) :
    m * (b + T) * k <
      ∑ c ∈ Uᶜ, (Cyl.incidence).colorDegree c := by
  have hscale : m * (b + T) * k ≤ m * (b + T) * T := by
    exact Nat.mul_le_mul_left (m * (b + T)) hk
  have hlt_pow : m * (b + T) * k < m ^ b :=
    lt_of_le_of_lt hscale hSlack
  exact hlt_pow.trans_le (D.sum_colorDegree_compl_lower_bound hU)

theorem slack_error_lt_sum_colorDegree_nonempty_min {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) {U : Finset (Fin (b + T))}
    (hU : U.Nonempty) (hSlack : m ^ b > m * (b + T) * T)
    (S : Finset (Fin T)) :
    m * (b + T) * min S.card (T - S.card) <
      ∑ c ∈ U, (Cyl.incidence).colorDegree c := by
  have hcard : S.card ≤ T := by
    simpa [Fintype.card_fin] using Finset.card_le_univ S
  have hmin : min S.card (T - S.card) ≤ T :=
    (Nat.min_le_left S.card (T - S.card)).trans hcard
  exact D.slack_error_lt_sum_colorDegree_nonempty hU hSlack
    hmin

theorem slack_error_lt_sum_colorDegree_compl_min {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) {U : Finset (Fin (b + T))}
    (hU : U ≠ Finset.univ) (hSlack : m ^ b > m * (b + T) * T)
    (S : Finset (Fin T)) :
    m * (b + T) * min S.card (T - S.card) <
      ∑ c ∈ Uᶜ, (Cyl.incidence).colorDegree c := by
  have hcard : S.card ≤ T := by
    simpa [Fintype.card_fin] using Finset.card_le_univ S
  have hmin : min S.card (T - S.card) ≤ T :=
    (Nat.min_le_left S.card (T - S.card)).trans hcard
  exact D.slack_error_lt_sum_colorDegree_compl hU hSlack
    hmin

theorem sum_colorDegree_le_T_mul_hitCount {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (_D : ActiveBlockData Cyl) (U : Finset (Fin (b + T))) :
    (∑ c ∈ U, (Cyl.incidence).colorDegree c) ≤
      T * (Cyl.incidence).hitCount U :=
  ActiveHall.Incidence.sum_colorDegree_on_le_hitCount_mul
    Cyl.incidence U

theorem slack_error_lt_T_mul_hitCount_nonempty {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) {U : Finset (Fin (b + T))}
    (hU : U.Nonempty) (hSlack : m ^ b > m * (b + T) * T)
    {k : Nat} (hk : k ≤ T) :
    m * (b + T) * k <
      T * (Cyl.incidence).hitCount U :=
  (D.slack_error_lt_sum_colorDegree_nonempty hU hSlack hk).trans_le
    (D.sum_colorDegree_le_T_mul_hitCount U)

theorem slack_error_lt_T_mul_hitCount_compl {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) {U : Finset (Fin (b + T))}
    (hU : U ≠ Finset.univ) (hSlack : m ^ b > m * (b + T) * T)
    {k : Nat} (hk : k ≤ T) :
    m * (b + T) * k <
      T * (Cyl.incidence).hitCount Uᶜ :=
  (D.slack_error_lt_sum_colorDegree_compl hU hSlack hk).trans_le
    (D.sum_colorDegree_le_T_mul_hitCount Uᶜ)

theorem slack_error_lt_T_mul_hitCount_nonempty_min {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) {U : Finset (Fin (b + T))}
    (hU : U.Nonempty) (hSlack : m ^ b > m * (b + T) * T)
    (S : Finset (Fin T)) :
    m * (b + T) * min S.card (T - S.card) <
      T * (Cyl.incidence).hitCount U :=
  (D.slack_error_lt_sum_colorDegree_nonempty_min hU hSlack S).trans_le
    (D.sum_colorDegree_le_T_mul_hitCount U)

theorem slack_error_lt_T_mul_hitCount_compl_min {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) {U : Finset (Fin (b + T))}
    (hU : U ≠ Finset.univ) (hSlack : m ^ b > m * (b + T) * T)
    (S : Finset (Fin T)) :
    m * (b + T) * min S.card (T - S.card) <
      T * (Cyl.incidence).hitCount Uᶜ :=
  (D.slack_error_lt_sum_colorDegree_compl_min hU hSlack S).trans_le
    (D.sum_colorDegree_le_T_mul_hitCount Uᶜ)

theorem sum_active_complement_eq {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) :
    (∑ c : Fin (b + T), (m - D.activeBlock c)) = T * m := by
  classical
  have hdegSum := ActiveHall.Incidence.sum_colorDegree Cyl.incidence
  have hleft :
      (∑ c : Fin (b + T), (Cyl.incidence).colorDegree c)
        =
      (∑ c : Fin (b + T), (m - D.activeBlock c)) * m ^ b := by
    calc
      (∑ c : Fin (b + T), (Cyl.incidence).colorDegree c)
          = ∑ c : Fin (b + T), (m - D.activeBlock c) * m ^ b := by
              apply Finset.sum_congr rfl
              intro c _hc
              exact D.active_degree_eq c
      _ = (∑ c : Fin (b + T), (m - D.activeBlock c)) * m ^ b := by
              rw [Finset.sum_mul]
  have hright :
      T * Fintype.card (Shared.TorusVertex (b + 1) m) =
        (T * m) * m ^ b := by
    rw [Shared.card_torusVertex, pow_succ]
    ring
  have hmul :
      (∑ c : Fin (b + T), (m - D.activeBlock c)) * m ^ b =
        (T * m) * m ^ b := by
    rw [← hleft, hdegSum, hright]
  exact Nat.mul_right_cancel
    (pow_pos (Nat.pos_of_ne_zero (NeZero.ne m)) b) hmul

theorem sum_activeBlock_eq {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) :
    (∑ c : Fin (b + T), D.activeBlock c) = b * m := by
  classical
  have hcomp := D.sum_active_complement_eq
  have hsum_add :
      (∑ c : Fin (b + T), D.activeBlock c) +
          (∑ c : Fin (b + T), (m - D.activeBlock c))
        =
      (b + T) * m := by
    calc
      (∑ c : Fin (b + T), D.activeBlock c) +
          (∑ c : Fin (b + T), (m - D.activeBlock c))
          = ∑ c : Fin (b + T), (D.activeBlock c + (m - D.activeBlock c)) := by
              rw [Finset.sum_add_distrib]
      _ = ∑ _c : Fin (b + T), m := by
              apply Finset.sum_congr rfl
              intro c _hc
              exact Nat.add_sub_of_le (Nat.le_of_lt (D.activeBlock_lt c))
      _ = (b + T) * m := by
              simp [Finset.sum_const, Fintype.card_fin]
  rw [hcomp] at hsum_add
  have htarget : (b + T) * m = b * m + T * m := by
    ring
  rw [htarget] at hsum_add
  exact Nat.add_right_cancel hsum_add

theorem isCylinder_of_activeBlockData {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (ordinary_unique :
      ∀ x : Shared.TorusVertex (b + 1) m,
        ∀ i : Fin (b + 1), i ≠ activeDir b →
          ∃! c : Fin (b + T), Cyl.dir c x = i)
    (color_hamiltonian :
      ∀ c : Fin (b + T), Shared.IsSingleCycleMap (Cyl.step c))
    (D : ActiveBlockData Cyl) (hb : 0 < b) :
    IsCylinder Cyl where
  ordinary_unique := ordinary_unique
  color_hamiltonian := color_hamiltonian
  active_degree_mod := D.active_degree_mod hb

end ActiveBlockData

namespace Cylinder

theorem active_fiber_card {b m T : Nat} {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets)
    (x : Shared.TorusVertex (b + 1) m) :
    ((Finset.univ : Finset (Fin (b + T))).filter
      (fun c => Cyl.dir c x = activeDir b)).card = T :=
  Cyl.active_card x

theorem active_direction_exists_of_pos {b m T : Nat}
    {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets)
    (x : Shared.TorusVertex (b + 1) m) (hT : 0 < T) :
    ∃ c : Fin (b + T), Cyl.dir c x = activeDir b := by
  classical
  have hcard := Cyl.active_fiber_card x
  have hpos :
      0 < ((Finset.univ : Finset (Fin (b + T))).filter
        (fun c => Cyl.dir c x = activeDir b)).card := by
    omega
  rcases Finset.card_pos.mp hpos with ⟨c, hc⟩
  exact ⟨c, (Finset.mem_filter.mp hc).2⟩

end Cylinder

namespace IsCylinder

theorem ordinary_direction_exists {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (hCyl : IsCylinder Cyl)
    (x : Shared.TorusVertex (b + 1) m)
    (i : Fin (b + 1)) (hi : i ≠ activeDir b) :
    ∃ c : Fin (b + T), Cyl.dir c x = i := by
  rcases hCyl.ordinary_unique x i hi with ⟨c, hc, _huniq⟩
  exact ⟨c, hc⟩

theorem ordinary_fiber_card {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (hCyl : IsCylinder Cyl)
    (x : Shared.TorusVertex (b + 1) m)
    (i : Fin (b + 1)) (hi : i ≠ activeDir b) :
    ((Finset.univ : Finset (Fin (b + T))).filter
      (fun c => Cyl.dir c x = i)).card = 1 := by
  classical
  rcases hCyl.ordinary_unique x i hi with ⟨c, hc, huniq⟩
  rw [Finset.card_eq_one]
  refine ⟨c, ?_⟩
  ext d
  constructor
  · intro hd
    rw [Finset.mem_filter] at hd
    simp [huniq d hd.2]
  · intro hd
    have hdc : d = c := by
      simpa using hd
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ d, ?_⟩
    rw [hdc]
    exact hc

theorem dir_fiber_card {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (hCyl : IsCylinder Cyl)
    (x : Shared.TorusVertex (b + 1) m)
    (i : Fin (b + 1)) :
    ((Finset.univ : Finset (Fin (b + T))).filter
      (fun c => Cyl.dir c x = i)).card =
        if i = activeDir b then T else 1 := by
  by_cases hi : i = activeDir b
  · subst i
    simp [Cylinder.active_fiber_card]
  · simp [hi, hCyl.ordinary_fiber_card x i hi]

end IsCylinder

namespace Cylinder

theorem step_activeDir_eq_of_dir_ne {b m T : Nat} {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets)
    (c : Fin (b + T)) (x : Shared.TorusVertex (b + 1) m)
    (hdir : Cyl.dir c x ≠ activeDir b) :
    (Cyl.step c x) (activeDir b) = x (activeDir b) := by
  simp [Cylinder.step, Shared.torusBasis, hdir.symm]

theorem dir_ne_activeDir_of_colorDegree_zero {b m T : Nat} [NeZero m]
    {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets)
    {c : Fin (b + T)}
    (hdeg : (Cyl.incidence).colorDegree c = 0)
    (x : Shared.TorusVertex (b + 1) m) :
    Cyl.dir c x ≠ activeDir b := by
  classical
  have hfilter_empty :
      ((Finset.univ : Finset (Shared.TorusVertex (b + 1) m)).filter
        (fun x => c ∈ (Cyl.incidence).active x)) = ∅ := by
    exact Finset.card_eq_zero.mp hdeg
  have hnot : c ∉ (Cyl.incidence).active x := by
    intro hc
    have hx :
        x ∈ ((Finset.univ : Finset (Shared.TorusVertex (b + 1) m)).filter
          (fun x => c ∈ (Cyl.incidence).active x)) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hc⟩
    rw [hfilter_empty] at hx
    simp at hx
  intro hdir
  exact hnot (by
    simp [Cylinder.incidence, Cylinder.active, hdir])

theorem iterate_step_activeDir_eq_of_colorDegree_zero
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets)
    {c : Fin (b + T)}
    (hdeg : (Cyl.incidence).colorDegree c = 0) :
    ∀ n : Nat, ∀ x : Shared.TorusVertex (b + 1) m,
      ((Cyl.step c)^[n] x) (activeDir b) = x (activeDir b)
  | 0, x => by simp
  | n + 1, x => by
      rw [Function.iterate_succ_apply']
      calc
        (Cyl.step c ((Cyl.step c)^[n] x)) (activeDir b)
            = ((Cyl.step c)^[n] x) (activeDir b) := by
                exact Cyl.step_activeDir_eq_of_dir_ne c ((Cyl.step c)^[n] x)
                  (Cyl.dir_ne_activeDir_of_colorDegree_zero hdeg
                    ((Cyl.step c)^[n] x))
        _ = x (activeDir b) :=
                Cyl.iterate_step_activeDir_eq_of_colorDegree_zero hdeg n x

end Cylinder

namespace IsCylinder

theorem active_degree_pos {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (hCyl : IsCylinder Cyl) (hm : 1 < m) (c : Fin (b + T)) :
    0 < (Cyl.incidence).colorDegree c := by
  classical
  by_contra hpos
  have hdeg : (Cyl.incidence).colorDegree c = 0 :=
    Nat.eq_zero_of_not_pos hpos
  let x0 : Shared.TorusVertex (b + 1) m := 0
  let y : Shared.TorusVertex (b + 1) m :=
    Shared.torusBasis (b + 1) m (activeDir b)
  rcases (hCyl.color_hamiltonian c).2 x0 y with ⟨n, hn⟩
  have hcoord := congrArg (fun x : Shared.TorusVertex (b + 1) m =>
    x (activeDir b)) hn
  have hiter :=
    Cyl.iterate_step_activeDir_eq_of_colorDegree_zero hdeg n x0
  have h01 : (0 : ZMod m) = 1 := by
    simpa [x0, y, Shared.torusBasis] using hiter.symm.trans hcoord
  have h10 : (1 : ZMod m) ≠ 0 := by
    intro h
    have h' : ((1 : Nat) : ZMod m) = 0 := by simpa using h
    have hdvd : m ∣ 1 := (ZMod.natCast_eq_zero_iff 1 m).mp h'
    have hmle : m ≤ 1 := Nat.le_of_dvd (by decide : 0 < 1) hdvd
    omega
  exact h10 h01.symm

theorem active_degree_dvd_modulus {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (hCyl : IsCylinder Cyl) (c : Fin (b + T)) :
    m ∣ (Cyl.incidence).colorDegree c := by
  exact (ZMod.natCast_eq_zero_iff ((Cyl.incidence).colorDegree c) m).mp
    (hCyl.active_degree_mod c)

theorem modulus_le_active_degree {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (hCyl : IsCylinder Cyl) (hm : 1 < m) (c : Fin (b + T)) :
    m ≤ (Cyl.incidence).colorDegree c := by
  exact Nat.le_of_dvd (hCyl.active_degree_pos hm c)
    (hCyl.active_degree_dvd_modulus c)

end IsCylinder

structure ActiveSymboling {b m T : Nat} [NeZero m]
    {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets) where
  R : ActiveHall.ResidueSpec m T (Fin (b + T))
  Φ : ActiveHall.Symboling Cyl.incidence

noncomputable def expandedColorDir
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets) (A : ActiveSymboling Cyl) :
    Shared.TorusColor (b + T) →
      Shared.TorusVertex (b + T) m →
      Shared.TorusDirection (b + T) :=
  fun c x =>
    let y := collapseVertex b m T x
    let i := Cyl.dir c y
    if hactive : i = activeDir b then
      tailExpandedDir b
        ((A.Φ.equiv y).symm
          ⟨c, by
            change c ∈ Cyl.active y
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hactive⟩⟩)
    else
      ordinaryExpandedDir i hactive

structure IsActiveSymboling {b m T : Nat} [NeZero m]
    {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (A : ActiveSymboling Cyl) : Prop where
  has_residues : A.Φ.HasResidues A.R

def IsPrimitiveActiveSymboling {b m T : Nat} [NeZero m]
    {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hT : 2 ≤ T) (A : ActiveSymboling Cyl) : Prop :=
  IsActiveSymboling A ∧
    (∀ c : Fin (b + T), IsUnit (A.R.target c ⟨0, by omega⟩)) ∧
    (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
      IsUnit (A.R.target c σ - A.R.target c ⟨1, by omega⟩))

/--
The local geometric assembly theorem still needed for the primitive lift.

This deliberately omits packet arithmetic, slack, and the solved base
hypothesis: those are used to construct the cylinder and its primitive active
symboling.  Once those objects exist, the remaining content is to expand the
compressed base-tail cylinder into a Cayley Hamilton decomposition in dimension
`b + T`.
-/
def PrimitiveActiveLiftAssemblyGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets} {A : ActiveSymboling Cyl}
    (hT : 2 ≤ T),
      IsCylinder Cyl →
      IsPrimitiveActiveSymboling hT A →
      Shared.CayleyHamiltonDecomposition (b + T) m

def ExpandedColorDirEdgePartitionGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets} {A : ActiveSymboling Cyl},
      IsCylinder Cyl →
      Shared.IsCayleyEdgePartition (expandedColorDir Cyl A)

def ExpandedColorDirColorHamiltonianGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets} {A : ActiveSymboling Cyl}
    (hT : 2 ≤ T),
      IsCylinder Cyl →
      IsPrimitiveActiveSymboling hT A →
      Shared.IsCayleyColorHamiltonian (expandedColorDir Cyl A)

theorem primitiveActiveLiftAssemblyGoal_of_expandedColorDirPieces
    (hEdge : ExpandedColorDirEdgePartitionGoal)
    (hHam : ExpandedColorDirColorHamiltonianGoal) :
    PrimitiveActiveLiftAssemblyGoal := by
  intro b m T _inst packets Cyl A hT hCyl hA
  exact ⟨{
    colorDir := expandedColorDir Cyl A
    edgePartition := hEdge hCyl
    colorHamiltonian := hHam hT hCyl hA
  }⟩

theorem expandedColorDirEdgePartitionGoal :
    ExpandedColorDirEdgePartitionGoal := by
  classical
  intro b m T _inst packets Cyl A hCyl x j
  let y := collapseVertex b m T x
  by_cases hj : j.val < b
  · let i : Fin (b + 1) := ordinaryBaseDirOfExpandedDir j hj
    have hi : i ≠ activeDir b :=
      ordinaryBaseDirOfExpandedDir_ne_active j hj
    rcases hCyl.ordinary_unique y i hi with ⟨c, hc, huniq⟩
    refine ⟨c, ?_, ?_⟩
    · have hnot : Cyl.dir c y ≠ activeDir b := by
        rw [hc]
        exact hi
      apply Fin.ext
      simp [expandedColorDir, y, hi, ordinaryExpandedDir, hc]
      rfl
    · intro d hd
      have hnot : Cyl.dir d y ≠ activeDir b := by
        intro hactive
        have hval := congrArg Fin.val hd
        have hge : b ≤ (expandedColorDir Cyl A d x).val := by
          simp [expandedColorDir, y, hactive, tailExpandedDir]
        rw [hval] at hge
        omega
      have hdir : Cyl.dir d y = i := by
        apply Fin.ext
        have hval := congrArg Fin.val hd
        have hval' :
            (expandedColorDir Cyl A d x).val = (Cyl.dir d y).val := by
          simp [expandedColorDir, y, hnot, ordinaryExpandedDir]
        rw [hval'] at hval
        simpa [i, ordinaryBaseDirOfExpandedDir] using hval
      exact huniq d hdir
  · have hjge : b ≤ j.val := by omega
    let σ : Fin T := tailSymbolOfExpandedDir j hjge
    let p : {c : Fin (b + T) // c ∈ (Cyl.incidence).active y} :=
      A.Φ.equiv y σ
    let c : Fin (b + T) := p.1
    have hcActive : Cyl.dir c y = activeDir b := by
      have hp : c ∈ Cyl.active y := by
        simp [Cylinder.incidence, c, p]
      exact (Finset.mem_filter.mp hp).2
    have hsub :
        (⟨c, by
          change c ∈ Cyl.active y
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hcActive⟩⟩ :
          {c : Fin (b + T) // c ∈ (Cyl.incidence).active y}) = p := by
      apply Subtype.ext
      rfl
    have hsymm :
        (A.Φ.equiv y).symm
          (⟨c, by
            change c ∈ Cyl.active y
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hcActive⟩⟩ :
            {c : Fin (b + T) // c ∈ (Cyl.incidence).active y}) = σ := by
      rw [hsub]
      exact (A.Φ.equiv y).symm_apply_apply σ
    refine ⟨c, ?_, ?_⟩
    · calc
        expandedColorDir Cyl A c x = tailExpandedDir b σ := by
          simp [expandedColorDir, y, hcActive, hsymm]
        _ = j := tailExpandedDir_of_tailSymbol j hjge
    · intro d hd
      have hactive : Cyl.dir d y = activeDir b := by
        by_contra hnot
        have hval := congrArg Fin.val hd
        have hlt : (expandedColorDir Cyl A d x).val < b := by
          simp [expandedColorDir, y, hnot, ordinaryExpandedDir_val_lt]
        rw [hval] at hlt
        omega
      have hdmem : d ∈ Cyl.active y :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ d, hactive⟩
      let q : {c : Fin (b + T) // c ∈ (Cyl.incidence).active y} :=
        ⟨d, by
          change d ∈ Cyl.active y
          exact hdmem⟩
      have hsymm_d : (A.Φ.equiv y).symm q = σ := by
        have hbranch :
            expandedColorDir Cyl A d x =
              tailExpandedDir b ((A.Φ.equiv y).symm q) := by
          simp [expandedColorDir, y, hactive, q]
        apply tailExpandedDir_injective (b := b)
        rw [← hbranch, hd]
        exact (tailExpandedDir_of_tailSymbol j hjge).symm
      have hq : q = p := by
        have happly := congrArg (A.Φ.equiv y) hsymm_d
        simpa [q, p] using happly
      exact congrArg Subtype.val hq

theorem primitiveActiveLiftAssemblyGoal_of_expandedColorDirHamiltonian
    (hHam : ExpandedColorDirColorHamiltonianGoal) :
    PrimitiveActiveLiftAssemblyGoal :=
  primitiveActiveLiftAssemblyGoal_of_expandedColorDirPieces
    expandedColorDirEdgePartitionGoal hHam

def HasFeasiblePrimitiveResidues {b m T : Nat} [NeZero m]
    {packets : List (List Nat)}
    (hT : 2 ≤ T) (Cyl : Cylinder b m T packets) : Prop :=
  ∃ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
    ActiveHall.FeasibleWithResidues Cyl.incidence R ∧
      (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) ∧
      (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
        IsUnit (R.target c σ - R.target c ⟨1, by omega⟩))

theorem activeSymboling_of_feasible_and_hallRealization
    (hHall : ActiveHall.HallRealizationGoal.{0, 0})
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets)
    (R : ActiveHall.ResidueSpec m T (Fin (b + T)))
    (hFeasible : ActiveHall.FeasibleWithResidues Cyl.incidence R) :
    ∃ A : ActiveSymboling Cyl, IsActiveSymboling A := by
  rcases
    ActiveHall.symbolingWithResidues_of_feasible_and_realization
      hHall hFeasible with
    ⟨Φ, hΦ⟩
  exact ⟨{ R := R, Φ := Φ }, ⟨hΦ⟩⟩

theorem primitiveActiveSymboling_of_feasible_primitiveResidue_and_hallRealization
    (hHall : ActiveHall.HallRealizationGoal.{0, 0})
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    (hT : 2 ≤ T) (Cyl : Cylinder b m T packets)
    (R : ActiveHall.ResidueSpec m T (Fin (b + T)))
    (hFeasible : ActiveHall.FeasibleWithResidues Cyl.incidence R)
    (hZero : ∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩))
    (hNumeric : ∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
      IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) :
    ∃ A : ActiveSymboling Cyl, IsPrimitiveActiveSymboling hT A := by
  rcases
    ActiveHall.symbolingWithResidues_of_feasible_and_realization
      hHall hFeasible with
    ⟨Φ, hΦ⟩
  exact ⟨{ R := R, Φ := Φ }, ⟨⟨hΦ⟩, hZero, hNumeric⟩⟩

theorem primitiveActiveSymboling_of_feasiblePrimitiveResidues_and_hallRealization
    (hHall : ActiveHall.HallRealizationGoal.{0, 0})
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets} {hT : 2 ≤ T}
    (hResidues : HasFeasiblePrimitiveResidues hT Cyl) :
    ∃ A : ActiveSymboling Cyl, IsPrimitiveActiveSymboling hT A := by
  rcases hResidues with ⟨R, hFeasible, hZero, hNumeric⟩
  exact
    primitiveActiveSymboling_of_feasible_primitiveResidue_and_hallRealization
      hHall hT Cyl R hFeasible hZero hNumeric

theorem exists_universalResidueSpec_compatible_primitive_of_cylinder
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hT : 2 ≤ T) (hCyl : IsCylinder Cyl)
    (hdodd : Odd (b + T)) (hd3 : 3 ≤ b + T) (hmodd : Odd m) :
    ∃ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
      R.RowCompatible Cyl.incidence ∧ R.ColCompatible Cyl.incidence ∧
      (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) ∧
      (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
        IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) := by
  classical
  have hX :
      (Fintype.card (Shared.TorusVertex (b + 1) m) : ZMod m) = 0 := by
    rw [Shared.card_torusVertex]
    exact ActiveHall.zmod_natCast_pow_eq_zero_of_pos (Nat.succ_pos b)
  exact
    ActiveHall.exists_universalUnitResidueSpecOfTwoLe_compatible_primitive
      hT Cyl.incidence hdodd hd3 hmodd hCyl.active_degree_mod hX

theorem exists_universalResidueSpec_compatible_primitive_of_successor_cylinder
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hb5 : 5 ≤ b) (hT : T = b + 1) (hmodd : Odd m)
    (hCyl : IsCylinder Cyl) :
    ∃ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
      R.RowCompatible Cyl.incidence ∧ R.ColCompatible Cyl.incidence ∧
      (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) ∧
      (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
        IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) := by
  have hT2 : 2 ≤ T := by omega
  have hdodd : Odd (b + T) := by
    rw [hT]
    exact ⟨b, by omega⟩
  have hd3 : 3 ≤ b + T := by omega
  exact exists_universalResidueSpec_compatible_primitive_of_cylinder
    hT2 hCyl hdodd hd3 hmodd

theorem exists_universalResidueSpec_compatible_primitive_of_activeBlockData
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hT : 2 ≤ T) (D : ActiveBlockData Cyl) (hb : 0 < b)
    (hdodd : Odd (b + T)) (hd3 : 3 ≤ b + T) (hmodd : Odd m) :
    ∃ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
      R.RowCompatible Cyl.incidence ∧ R.ColCompatible Cyl.incidence ∧
      (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) ∧
      (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
        IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) := by
  classical
  have hX :
      (Fintype.card (Shared.TorusVertex (b + 1) m) : ZMod m) = 0 := by
    rw [Shared.card_torusVertex]
    exact ActiveHall.zmod_natCast_pow_eq_zero_of_pos (Nat.succ_pos b)
  exact
    ActiveHall.exists_universalUnitResidueSpecOfTwoLe_compatible_primitive
      hT Cyl.incidence hdodd hd3 hmodd (D.active_degree_mod hb) hX

theorem exists_universalResidueSpec_compatible_primitive_of_successor_activeBlockData
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hb5 : 5 ≤ b) (hT : T = b + 1) (hmodd : Odd m)
    (D : ActiveBlockData Cyl) :
    ∃ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
      R.RowCompatible Cyl.incidence ∧ R.ColCompatible Cyl.incidence ∧
      (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) ∧
      (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
        IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) := by
  have hT2 : 2 ≤ T := by omega
  have hbpos : 0 < b := by omega
  have hdodd : Odd (b + T) := by
    rw [hT]
    exact ⟨b, by omega⟩
  have hd3 : 3 ≤ b + T := by omega
  exact exists_universalResidueSpec_compatible_primitive_of_activeBlockData
    hT2 D hbpos hdodd hd3 hmodd

theorem feasiblePrimitiveResidues_of_successor_cylinder_feasible_compatible
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hb5 : 5 ≤ b) (hT : T = b + 1) (hmodd : Odd m)
    (hCyl : IsCylinder Cyl)
    (hFeasible :
      ∀ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
        R.RowCompatible Cyl.incidence →
        R.ColCompatible Cyl.incidence →
        (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) →
        (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
          IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) →
        ActiveHall.FeasibleWithResidues Cyl.incidence R) :
    HasFeasiblePrimitiveResidues (by omega : 2 ≤ T) Cyl := by
  rcases
    exists_universalResidueSpec_compatible_primitive_of_successor_cylinder
      hb5 hT hmodd hCyl with
    ⟨R, hRow, hCol, hZero, hNumeric⟩
  exact ⟨R, hFeasible R hRow hCol hZero hNumeric, hZero, hNumeric⟩

theorem feasiblePrimitiveResidues_of_successor_activeBlockData_feasible_compatible
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hb5 : 5 ≤ b) (hT : T = b + 1) (hmodd : Odd m)
    (D : ActiveBlockData Cyl)
    (hFeasible :
      ∀ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
        R.RowCompatible Cyl.incidence →
        R.ColCompatible Cyl.incidence →
        (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) →
        (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
          IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) →
        ActiveHall.FeasibleWithResidues Cyl.incidence R) :
    HasFeasiblePrimitiveResidues (by omega : 2 ≤ T) Cyl := by
  rcases
    exists_universalResidueSpec_compatible_primitive_of_successor_activeBlockData
      hb5 hT hmodd D with
    ⟨R, hRow, hCol, hZero, hNumeric⟩
  exact ⟨R, hFeasible R hRow hCol hZero hNumeric, hZero, hNumeric⟩

theorem primitiveActiveSymboling_of_successor_cylinder_feasible_compatible
    (hHall : ActiveHall.HallRealizationGoal.{0, 0})
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hb5 : 5 ≤ b) (hT : T = b + 1) (hmodd : Odd m)
    (hCyl : IsCylinder Cyl)
    (hFeasible :
      ∀ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
        R.RowCompatible Cyl.incidence →
        R.ColCompatible Cyl.incidence →
        (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) →
        (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
          IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) →
        ActiveHall.FeasibleWithResidues Cyl.incidence R) :
    ∃ A : ActiveSymboling Cyl,
      IsPrimitiveActiveSymboling (by omega : 2 ≤ T) A := by
  exact
    primitiveActiveSymboling_of_feasiblePrimitiveResidues_and_hallRealization
      hHall
      (feasiblePrimitiveResidues_of_successor_cylinder_feasible_compatible
        hb5 hT hmodd hCyl hFeasible)

theorem primitiveActiveSymboling_of_successor_activeBlockData_feasible_compatible
    (hHall : ActiveHall.HallRealizationGoal.{0, 0})
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hb5 : 5 ≤ b) (hT : T = b + 1) (hmodd : Odd m)
    (D : ActiveBlockData Cyl)
    (hFeasible :
      ∀ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
        R.RowCompatible Cyl.incidence →
        R.ColCompatible Cyl.incidence →
        (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) →
        (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
          IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) →
        ActiveHall.FeasibleWithResidues Cyl.incidence R) :
    ∃ A : ActiveSymboling Cyl,
      IsPrimitiveActiveSymboling (by omega : 2 ≤ T) A := by
  exact
    primitiveActiveSymboling_of_feasiblePrimitiveResidues_and_hallRealization
      hHall
      (feasiblePrimitiveResidues_of_successor_activeBlockData_feasible_compatible
        hb5 hT hmodd D hFeasible)

lemma list_sum_ge_mul_of_forall_ge {k : Nat} :
    ∀ {xs : List Nat}, (∀ x, x ∈ xs → k ≤ x) → k * xs.length ≤ xs.sum
  | [], _h => by simp
  | x :: xs, h => by
      have hx : k ≤ x := h x (by simp)
      have hxs : ∀ y, y ∈ xs → k ≤ y := by
        intro y hy
        exact h y (by simp [hy])
      have ih := list_sum_ge_mul_of_forall_ge (k := k) hxs
      simp at ih ⊢
      nlinarith

lemma list_all_eq_of_sum_eq_mul {k : Nat} :
    ∀ {xs : List Nat},
      (∀ x, x ∈ xs → k ≤ x) → xs.sum = k * xs.length →
      ∀ x, x ∈ xs → x = k
  | [], _hge, _hsum, _x, hx => by simp at hx
  | x :: xs, hge, hsum, y, hy => by
      have hxge : k ≤ x := hge x (by simp)
      have hxsge : ∀ z, z ∈ xs → k ≤ z := by
        intro z hz
        exact hge z (by simp [hz])
      have htail_ge := list_sum_ge_mul_of_forall_ge (k := k) hxsge
      have hxle : x ≤ k := by
        simp at hsum
        simp at htail_ge
        nlinarith
      have hx : x = k := by omega
      have htail_sum : xs.sum = k * xs.length := by
        simp [hx] at hsum
        nlinarith
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hx
      · exact list_all_eq_of_sum_eq_mul (k := k) hxsge htail_sum y hy

lemma list_entries_two_or_three_of_sum_eq_two_len_add_one :
    ∀ {xs : List Nat},
      (∀ x, x ∈ xs → 2 ≤ x) → xs.sum = 2 * xs.length + 1 →
      ∀ x, x ∈ xs → x = 2 ∨ x = 3
  | [], _hge, _hsum, _x, hx => by simp at hx
  | x :: xs, hge, hsum, y, hy => by
      have hxge : 2 ≤ x := hge x (by simp)
      have hxsge : ∀ z, z ∈ xs → 2 ≤ z := by
        intro z hz
        exact hge z (by simp [hz])
      have htail_ge := list_sum_ge_mul_of_forall_ge (k := 2) hxsge
      have hxle : x ≤ 3 := by
        simp at hsum
        simp at htail_ge
        nlinarith
      have hx23 : x = 2 ∨ x = 3 := by omega
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hx23
      · rcases hx23 with hx | hx
        · have htail_sum : xs.sum = 2 * xs.length + 1 := by
            simp [hx] at hsum
            nlinarith
          exact list_entries_two_or_three_of_sum_eq_two_len_add_one
            hxsge htail_sum y hy
        · have htail_sum : xs.sum = 2 * xs.length := by
            simp [hx] at hsum
            nlinarith
          left
          exact list_all_eq_of_sum_eq_mul (k := 2) hxsge htail_sum y hy

lemma list_filter_eq_three_length_eq_one_of_sum_eq_two_len_add_one :
    ∀ {xs : List Nat},
      (∀ x, x ∈ xs → 2 ≤ x) → xs.sum = 2 * xs.length + 1 →
      (xs.filter (fun x => x = 3)).length = 1
  | [], _hge, hsum => by simp at hsum
  | x :: xs, hge, hsum => by
      have hxge : 2 ≤ x := hge x (by simp)
      have hxsge : ∀ z, z ∈ xs → 2 ≤ z := by
        intro z hz
        exact hge z (by simp [hz])
      have htail_ge := list_sum_ge_mul_of_forall_ge (k := 2) hxsge
      have hxle : x ≤ 3 := by
        simp at hsum
        simp at htail_ge
        nlinarith
      have hx23 : x = 2 ∨ x = 3 := by omega
      rcases hx23 with hx | hx
      · have htail_sum : xs.sum = 2 * xs.length + 1 := by
          simp [hx] at hsum
          nlinarith
        have ih :=
          list_filter_eq_three_length_eq_one_of_sum_eq_two_len_add_one
            hxsge htail_sum
        simp [hx, ih]
      · have htail_sum : xs.sum = 2 * xs.length := by
          simp [hx] at hsum
          nlinarith
        have htail_all_two :
            ∀ y, y ∈ xs → y = 2 :=
          list_all_eq_of_sum_eq_mul (k := 2) hxsge htail_sum
        have hfilter_empty : xs.filter (fun y => y = 3) = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro y hy
          rw [List.mem_filter] at hy
          have hy2 := htail_all_two y hy.1
          have hy3 : y = 3 := of_decide_eq_true hy.2
          omega
        simp [hx, hfilter_empty]

lemma packet_length_ge_two
    {m : Nat} (hm3 : 3 ≤ m) {packet : List Nat}
    (hsum : packet.sum = m)
    (hunit : ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) :
    2 ≤ packet.length := by
  cases packet with
  | nil =>
      simp at hsum
      omega
  | cons a tail =>
      cases tail with
      | nil =>
          have ha := hunit a (by simp)
          simp at hsum
          omega
      | cons _b _rest =>
          simp

lemma packet_proper_prefix_sum_coprime_of_length_two_or_three
    {m : Nat} {packet : List Nat}
    (hsum : packet.sum = m)
    (hunit : ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m)
    (hlen : packet.length = 2 ∨ packet.length = 3)
    {q : Nat} (hqpos : 0 < q) (hqproper : q < packet.length) :
    Nat.Coprime (packet.take q).sum m := by
  cases packet with
  | nil =>
      simp at hlen
  | cons a tail =>
      cases tail with
      | nil =>
          simp at hlen
      | cons b tail2 =>
          cases tail2 with
          | nil =>
              have hq : q = 1 := by
                simp at hqproper
                omega
              subst q
              have ha := hunit a (by simp)
              simpa using ha.2.2
          | cons c tail3 =>
              cases tail3 with
              | nil =>
                  have hq : q = 1 ∨ q = 2 := by
                    simp at hqproper
                    omega
                  rcases hq with rfl | rfl
                  · have ha := hunit a (by simp)
                    simpa using ha.2.2
                  · have hc := hunit c (by simp)
                    have hsumabc : a + b + c = m := by
                      simpa [Nat.add_assoc] using hsum
                    have hc_le : c ≤ m := by omega
                    have hab_eq : a + b = m - c := by omega
                    rw [show (List.take 2 [a, b, c]).sum = a + b by simp]
                    rw [hab_eq]
                    exact (Nat.coprime_self_sub_left hc_le).2 hc.2.2
              | cons _d _rest =>
                  simp at hlen

lemma packet_proper_prefix_sum_range_of_length_two_or_three
    {m : Nat} {packet : List Nat}
    (hsum : packet.sum = m)
    (hunit : ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m)
    (hlen : packet.length = 2 ∨ packet.length = 3)
    {q : Nat} (hqpos : 0 < q) (hqproper : q < packet.length) :
    0 < (packet.take q).sum ∧ (packet.take q).sum < m := by
  cases packet with
  | nil =>
      simp at hlen
  | cons a tail =>
      cases tail with
      | nil =>
          simp at hlen
      | cons b tail2 =>
          cases tail2 with
          | nil =>
              have hq : q = 1 := by
                simp at hqproper
                omega
              subst q
              have ha := hunit a (by simp)
              simpa using And.intro ha.1 ha.2.1
          | cons c tail3 =>
              cases tail3 with
              | nil =>
                  have hq : q = 1 ∨ q = 2 := by
                    simp at hqproper
                    omega
                  rcases hq with rfl | rfl
                  · have ha := hunit a (by simp)
                    simpa using And.intro ha.1 ha.2.1
                  · have hc := hunit c (by simp)
                    have hsumabc : a + b + c = m := by
                      simpa [Nat.add_assoc] using hsum
                    rw [show (List.take 2 [a, b, c]).sum = a + b by simp]
                    omega
              | cons _d _rest =>
                  simp at hlen

def SuccessorPacketLengthTwoOrThreeGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∀ packet, packet ∈ packets → packet.length = 2 ∨ packet.length = 3

theorem successorPacketLengthTwoOrThreeGoal :
    SuccessorPacketLengthTwoOrThreeGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit
  let lengths : List Nat := packets.map List.length
  have hge : ∀ x, x ∈ lengths → 2 ≤ x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨packet, hp, rfl⟩
    exact packet_length_ge_two hm3 (hpacketSum packet hp) (hunit packet hp)
  have hsum : lengths.sum = 2 * lengths.length + 1 := by
    dsimp [lengths]
    rw [List.length_map, hlen, htotal, hT]
    omega
  have hlengths := list_entries_two_or_three_of_sum_eq_two_len_add_one hge hsum
  intro packet hp
  exact hlengths packet.length (List.mem_map.mpr ⟨packet, hp, rfl⟩)

def SuccessorPacketLengthThreeCountGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ((packets.map List.length).filter (fun len => len = 3)).length = 1

theorem successorPacketLengthThreeCountGoal :
    SuccessorPacketLengthThreeCountGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit
  let lengths : List Nat := packets.map List.length
  have hge : ∀ x, x ∈ lengths → 2 ≤ x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨packet, hp, rfl⟩
    exact packet_length_ge_two hm3 (hpacketSum packet hp) (hunit packet hp)
  have hsum : lengths.sum = 2 * lengths.length + 1 := by
    dsimp [lengths]
    rw [List.length_map, hlen, htotal, hT]
    omega
  exact
    list_filter_eq_three_length_eq_one_of_sum_eq_two_len_add_one hge hsum

lemma list_map_length_filter_eq_filter_length_length
    (packets : List (List Nat)) :
    ((packets.map List.length).filter (fun len => len = 3)).length
      =
    (packets.filter (fun packet => packet.length = 3)).length := by
  induction packets with
  | nil =>
      simp
  | cons packet packets ih =>
      by_cases h : packet.length = 3 <;> simp [h, ih]

lemma exists_unique_of_filter_length_eq_one {α : Type*}
    (f : α → Bool) :
    ∀ {xs : List α}, (xs.filter f).length = 1 →
      ∃ x, x ∈ xs ∧ f x = true ∧
        ∀ y, y ∈ xs → f y = true → y = x
  | [], h => by simp at h
  | x :: xs, h => by
      cases hx : f x
      · have htail : (xs.filter f).length = 1 := by
          simpa [hx] using h
        rcases exists_unique_of_filter_length_eq_one f htail with
          ⟨z, hzmem, hzf, hzuniq⟩
        refine ⟨z, by simp [hzmem], hzf, ?_⟩
        intro y hymem hyf
        simp only [List.mem_cons] at hymem
        rcases hymem with rfl | hytail
        · simp [hx] at hyf
        · exact hzuniq y hytail hyf
      · have htail_zero : (xs.filter f).length = 0 := by
          simpa [hx] using h
        refine ⟨x, by simp, hx, ?_⟩
        intro y hymem hyf
        simp only [List.mem_cons] at hymem
        rcases hymem with rfl | hytail
        · rfl
        · have hyfilter : y ∈ xs.filter f := by
            simp [hytail, hyf]
          have hfilter_nil : xs.filter f = [] :=
            List.length_eq_zero_iff.mp htail_zero
          simp [hfilter_nil] at hyfilter

def SuccessorPacketLengthThreePacketCountGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    (packets.filter (fun packet => packet.length = 3)).length = 1

theorem successorPacketLengthThreePacketCountGoal :
    SuccessorPacketLengthThreePacketCountGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit
  have hlengths :=
    successorPacketLengthThreeCountGoal
      hm3 hT hlen htotal hpacketSum hunit
  rw [← list_map_length_filter_eq_filter_length_length packets]
  exact hlengths

def SuccessorPacketExistsUniqueLengthThreeGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∃ packet, packet ∈ packets ∧ packet.length = 3 ∧
      ∀ other, other ∈ packets → other.length = 3 → other = packet

theorem successorPacketExistsUniqueLengthThreeGoal :
    SuccessorPacketExistsUniqueLengthThreeGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit
  have hcount :=
    successorPacketLengthThreePacketCountGoal
      hm3 hT hlen htotal hpacketSum hunit
  rcases exists_unique_of_filter_length_eq_one
      (fun packet : List Nat => packet.length = 3) hcount with
    ⟨packet, hmem, hlen3Bool, huniq⟩
  have hlen3 : packet.length = 3 := of_decide_eq_true hlen3Bool
  refine ⟨packet, hmem, hlen3, ?_⟩
  intro other hother hother3
  exact huniq other hother (decide_eq_true hother3)

def SuccessorPacketNonExceptionalLengthTwoGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∀ packet, packet ∈ packets → packet.length ≠ 3 → packet.length = 2

theorem successorPacketNonExceptionalLengthTwoGoal :
    SuccessorPacketNonExceptionalLengthTwoGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit packet hp hne
  have h23 :=
    successorPacketLengthTwoOrThreeGoal
      hm3 hT hlen htotal hpacketSum hunit packet hp
  rcases h23 with h2 | h3
  · exact h2
  · exact False.elim (hne h3)

def SuccessorPacketExceptionalShapeGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∃ exceptional, exceptional ∈ packets ∧ exceptional.length = 3 ∧
      ∀ packet, packet ∈ packets →
        packet = exceptional ∨ packet.length = 2

theorem successorPacketExceptionalShapeGoal :
    SuccessorPacketExceptionalShapeGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit
  rcases successorPacketExistsUniqueLengthThreeGoal
      hm3 hT hlen htotal hpacketSum hunit with
    ⟨exceptional, hexMem, hexLen, huniq⟩
  refine ⟨exceptional, hexMem, hexLen, ?_⟩
  intro packet hp
  by_cases hlen3 : packet.length = 3
  · left
    exact huniq packet hp hlen3
  · right
    exact successorPacketNonExceptionalLengthTwoGoal
      hm3 hT hlen htotal hpacketSum hunit packet hp hlen3

def SuccessorPacketProperPrefixUnitsGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∀ packet, packet ∈ packets →
      ∀ q : Nat, 0 < q → q < packet.length →
        Nat.Coprime (packet.take q).sum m

theorem successorPacketProperPrefixUnitsGoal :
    SuccessorPacketProperPrefixUnitsGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit
  have hlen23 :=
    successorPacketLengthTwoOrThreeGoal hm3 hT hlen htotal hpacketSum hunit
  intro packet hp q hqpos hqproper
  exact packet_proper_prefix_sum_coprime_of_length_two_or_three
    (hpacketSum packet hp) (hunit packet hp) (hlen23 packet hp) hqpos hqproper

def SuccessorPacketProperPrefixRangeGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∀ packet, packet ∈ packets →
      ∀ q : Nat, 0 < q → q < packet.length →
        0 < (packet.take q).sum ∧ (packet.take q).sum < m

theorem successorPacketProperPrefixRangeGoal :
    SuccessorPacketProperPrefixRangeGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit
  have hlen23 :=
    successorPacketLengthTwoOrThreeGoal hm3 hT hlen htotal hpacketSum hunit
  intro packet hp q hqpos hqproper
  exact packet_proper_prefix_sum_range_of_length_two_or_three
    (hpacketSum packet hp) (hunit packet hp) (hlen23 packet hp) hqpos hqproper

lemma list_sum_map_length_sub_one_add_length :
    ∀ {packets : List (List Nat)},
      (∀ packet, packet ∈ packets → 1 ≤ packet.length) →
      (packets.map (fun packet => packet.length - 1)).sum + packets.length =
        (packets.map List.length).sum
  | [], _h => by simp
  | packet :: packets, h => by
      have hp : 1 ≤ packet.length := h packet (by simp)
      have htail : ∀ p, p ∈ packets → 1 ≤ p.length := by
        intro p hpMem
        exact h p (by simp [hpMem])
      have ih := list_sum_map_length_sub_one_add_length htail
      simp at ih ⊢
      omega

lemma list_sum_map_eq_sum_get {α : Type*} (f : α → Nat) :
    ∀ (xs : List α), (∑ i : Fin xs.length, f (xs.get i)) = (xs.map f).sum
  | [] => by simp
  | x :: xs => by
      change (∑ i : Fin (xs.length + 1), f ((x :: xs).get i)) =
        f x + (xs.map f).sum
      rw [Fin.sum_univ_succ]
      simp

def PacketPrefixSlot (packets : List (List Nat)) : Type :=
  Sigma fun i : Fin packets.length => Fin ((packets.get i).length - 1)

instance (packets : List (List Nat)) : Fintype (PacketPrefixSlot packets) := by
  unfold PacketPrefixSlot
  infer_instance

def packetPrefixSlotPacket (packets : List (List Nat))
    (slot : PacketPrefixSlot packets) : List Nat :=
  packets.get slot.1

def packetPrefixSlotPrefixLength (packets : List (List Nat))
    (slot : PacketPrefixSlot packets) : Nat :=
  slot.2.val + 1

theorem packetPrefixSlotPrefixLength_pos (packets : List (List Nat))
    (slot : PacketPrefixSlot packets) :
    0 < packetPrefixSlotPrefixLength packets slot := by
  simp [packetPrefixSlotPrefixLength]

theorem packetPrefixSlotPrefixLength_lt (packets : List (List Nat))
    (slot : PacketPrefixSlot packets) :
    packetPrefixSlotPrefixLength packets slot <
      (packetPrefixSlotPacket packets slot).length := by
  dsimp [packetPrefixSlotPrefixLength, packetPrefixSlotPacket,
    PacketPrefixSlot] at *
  exact Nat.add_lt_of_lt_sub slot.2.isLt

theorem packetPrefixSlot_card_eq_sum (packets : List (List Nat)) :
    Fintype.card (PacketPrefixSlot packets) =
      (packets.map (fun packet => packet.length - 1)).sum := by
  change
    Fintype.card
      (Sigma fun i : Fin packets.length => Fin ((packets.get i).length - 1)) =
        (packets.map (fun packet => packet.length - 1)).sum
  rw [Fintype.card_sigma]
  simpa using
    list_sum_map_eq_sum_get (fun packet : List Nat => packet.length - 1)
      packets

def SuccessorPacketProperPrefixSlotCountGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    (packets.map (fun packet => packet.length - 1)).sum = T

theorem successorPacketProperPrefixSlotCountGoal :
    SuccessorPacketProperPrefixSlotCountGoal := by
  intro b m T packets hm3 hlen htotal hpacketSum hunit
  have hge : ∀ packet, packet ∈ packets → 1 ≤ packet.length := by
    intro packet hp
    have htwo : 2 ≤ packet.length :=
      packet_length_ge_two hm3 (hpacketSum packet hp) (hunit packet hp)
    omega
  have hsum :=
    list_sum_map_length_sub_one_add_length (packets := packets) hge
  rw [hlen, htotal] at hsum
  omega

def SuccessorPacketPrefixSlotCardGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    Fintype.card (PacketPrefixSlot packets) = T

theorem successorPacketPrefixSlotCardGoal :
    SuccessorPacketPrefixSlotCardGoal := by
  intro b m T packets hm3 hlen htotal hpacketSum hunit
  rw [packetPrefixSlot_card_eq_sum]
  exact successorPacketProperPrefixSlotCountGoal
    hm3 hlen htotal hpacketSum hunit

def SuccessorPacketPrefixSlotEquivGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    Nonempty (PacketPrefixSlot packets ≃ Fin T)

theorem successorPacketPrefixSlotEquivGoal :
    SuccessorPacketPrefixSlotEquivGoal := by
  intro b m T packets hm3 hlen htotal hpacketSum hunit
  have hcard : Fintype.card (PacketPrefixSlot packets) = Fintype.card (Fin T) := by
    rw [successorPacketPrefixSlotCardGoal hm3 hlen htotal hpacketSum hunit]
    simp
  exact ⟨Fintype.equivOfCardEq hcard⟩

def SuccessorPacketPrefixSlotUnitsGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∀ slot : PacketPrefixSlot packets,
      Nat.Coprime
        ((packetPrefixSlotPacket packets slot).take
          (packetPrefixSlotPrefixLength packets slot)).sum m

theorem successorPacketPrefixSlotUnitsGoal :
    SuccessorPacketPrefixSlotUnitsGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit slot
  exact successorPacketProperPrefixUnitsGoal
    hm3 hT hlen htotal hpacketSum hunit
    (packetPrefixSlotPacket packets slot)
    (List.get_mem packets slot.1)
    (packetPrefixSlotPrefixLength packets slot)
    (packetPrefixSlotPrefixLength_pos packets slot)
    (packetPrefixSlotPrefixLength_lt packets slot)

def SuccessorPacketPrefixSlotRangeGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∀ slot : PacketPrefixSlot packets,
      0 <
          ((packetPrefixSlotPacket packets slot).take
            (packetPrefixSlotPrefixLength packets slot)).sum ∧
        ((packetPrefixSlotPacket packets slot).take
            (packetPrefixSlotPrefixLength packets slot)).sum < m

theorem successorPacketPrefixSlotRangeGoal :
    SuccessorPacketPrefixSlotRangeGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit slot
  exact successorPacketProperPrefixRangeGoal
    hm3 hT hlen htotal hpacketSum hunit
    (packetPrefixSlotPacket packets slot)
    (List.get_mem packets slot.1)
    (packetPrefixSlotPrefixLength packets slot)
    (packetPrefixSlotPrefixLength_pos packets slot)
    (packetPrefixSlotPrefixLength_lt packets slot)

def SuccessorPacketTailCarryDataGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∃ carry : Fin T → Nat,
      ∀ σ : Fin T, 0 < carry σ ∧ carry σ < m ∧ Nat.Coprime (carry σ) m

theorem successorPacketTailCarryDataGoal :
    SuccessorPacketTailCarryDataGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit
  rcases successorPacketPrefixSlotEquivGoal
      hm3 hlen htotal hpacketSum hunit with ⟨e⟩
  let carry : Fin T → Nat := fun σ =>
    ((packetPrefixSlotPacket packets (e.symm σ)).take
      (packetPrefixSlotPrefixLength packets (e.symm σ))).sum
  refine ⟨carry, ?_⟩
  intro σ
  have hrange :=
    successorPacketPrefixSlotRangeGoal
      hm3 hT hlen htotal hpacketSum hunit (e.symm σ)
  have hunitCarry :=
    successorPacketPrefixSlotUnitsGoal
      hm3 hT hlen htotal hpacketSum hunit (e.symm σ)
  exact ⟨hrange.1, hrange.2, hunitCarry⟩

structure PacketTailCarryData (m T : Nat) (packets : List (List Nat)) where
  slotOf : Fin T ≃ PacketPrefixSlot packets
  carry : Fin T → Nat
  carry_eq :
    ∀ σ : Fin T,
      carry σ =
        ((packetPrefixSlotPacket packets (slotOf σ)).take
          (packetPrefixSlotPrefixLength packets (slotOf σ))).sum
  carry_pos : ∀ σ : Fin T, 0 < carry σ
  carry_lt : ∀ σ : Fin T, carry σ < m
  carry_coprime : ∀ σ : Fin T, Nat.Coprime (carry σ) m

namespace PacketTailCarryData

def residue {m T : Nat} {packets : List (List Nat)}
    (D : PacketTailCarryData m T packets) : Fin T → ZMod m :=
  fun σ => (D.carry σ : ZMod m)

theorem residue_isUnit {m T : Nat} {packets : List (List Nat)}
    (D : PacketTailCarryData m T packets) (σ : Fin T) :
    IsUnit (D.residue σ) := by
  exact (ZMod.isUnit_iff_coprime (D.carry σ) m).2 (D.carry_coprime σ)

end PacketTailCarryData

def SuccessorPacketTailCarryStructureGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    Nonempty (PacketTailCarryData m T packets)

theorem successorPacketTailCarryStructureGoal :
    SuccessorPacketTailCarryStructureGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit
  rcases successorPacketPrefixSlotEquivGoal
      hm3 hlen htotal hpacketSum hunit with ⟨e⟩
  let slotOf : Fin T ≃ PacketPrefixSlot packets := e.symm
  let carry : Fin T → Nat := fun σ =>
    ((packetPrefixSlotPacket packets (slotOf σ)).take
      (packetPrefixSlotPrefixLength packets (slotOf σ))).sum
  have hRange :
      ∀ σ : Fin T, 0 < carry σ ∧ carry σ < m := by
    intro σ
    exact successorPacketPrefixSlotRangeGoal
      hm3 hT hlen htotal hpacketSum hunit (slotOf σ)
  have hCoprime :
      ∀ σ : Fin T, Nat.Coprime (carry σ) m := by
    intro σ
    exact successorPacketPrefixSlotUnitsGoal
      hm3 hT hlen htotal hpacketSum hunit (slotOf σ)
  refine ⟨{
    slotOf := slotOf
    carry := carry
    carry_eq := ?_
    carry_pos := ?_
    carry_lt := ?_
    carry_coprime := hCoprime
  }⟩
  · intro σ
    rfl
  · intro σ
    exact (hRange σ).1
  · intro σ
    exact (hRange σ).2

def SuccessorPacketTailCarryResidueUnitsGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∃ carry : Fin T → ZMod m,
      ∀ σ : Fin T, IsUnit (carry σ)

theorem successorPacketTailCarryResidueUnitsGoal :
    SuccessorPacketTailCarryResidueUnitsGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit
  rcases successorPacketTailCarryDataGoal
      hm3 hT hlen htotal hpacketSum hunit with ⟨carryNat, hcarry⟩
  refine ⟨fun σ => (carryNat σ : ZMod m), ?_⟩
  intro σ
  exact (ZMod.isUnit_iff_coprime (carryNat σ) m).2 (hcarry σ).2.2

end BaseTail
end Concrete
end RoundComposite
