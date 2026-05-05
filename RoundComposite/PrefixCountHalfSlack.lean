import RoundComposite.PrefixCount

namespace RoundComposite
namespace PrefixCount

open scoped BigOperators

lemma exists_nat_shift_of_int_weight {n : Nat} (w : Fin n → Int) :
    ∃ (lo : Int) (u : Fin n → Nat) (D : Nat),
      (∀ i : Fin n, w i = lo + (u i : Int)) ∧
      (∀ i : Fin n, u i ≤ D) := by
  classical
  let S : Nat := ∑ i : Fin n, (w i).natAbs
  let lo : Int := - (S : Int)
  let u : Fin n → Nat := fun i => Int.toNat (w i - lo)
  refine ⟨lo, u, ∑ i : Fin n, u i, ?_, ?_⟩
  · intro i
    have hwi_le : w i ≤ (S : Int) := by
      have hterm : (w i).natAbs ≤ S := by
        dsimp [S]
        exact Finset.single_le_sum (s := Finset.univ)
          (f := fun j : Fin n => (w j).natAbs)
          (by intro j _hj; exact Nat.zero_le _) (Finset.mem_univ i)
      have hwi_abs : w i ≤ ((w i).natAbs : Int) := Int.le_natAbs
      exact le_trans hwi_abs (by exact_mod_cast hterm)
    have hneg_abs : - ((w i).natAbs : Int) ≤ w i := by
      rcases Int.natAbs_eq (w i) with h | h <;> rw [h] <;> omega
    have hnegS_le : - (S : Int) ≤ w i := by
      have hterm : ((w i).natAbs : Int) ≤ (S : Int) := by
        dsimp [S]
        exact_mod_cast Finset.single_le_sum (s := Finset.univ)
          (f := fun j : Fin n => (w j).natAbs)
          (by intro j _hj; exact Nat.zero_le _) (Finset.mem_univ i)
      nlinarith
    have hnonneg : 0 ≤ w i - lo := by
      dsimp [lo]
      omega
    have hto : ((Int.toNat (w i - lo) : Nat) : Int) = w i - lo :=
      Int.toNat_of_nonneg hnonneg
    dsimp [u]
    rw [hto]
    ring
  · intro i
    dsimp [u]
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin n => Int.toNat (w j - lo))
      (by intro j _hj; exact Nat.zero_le _) (Finset.mem_univ i)

lemma nat_eq_sum_upper_indicators {D u : Nat} (huD : u ≤ D) :
    (u : Int) =
      ∑ t ∈ Finset.range D, (if t < u then (1 : Int) else 0) := by
  classical
  have hfilter :
      (Finset.range D).filter (fun t => t < u) = Finset.range u := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      exact h.2
    · intro ht
      exact ⟨lt_of_lt_of_le ht huD, ht⟩
  calc
    (u : Int) = ((Finset.range u).card : Int) := by simp
    _ = (((Finset.range D).filter (fun t => t < u)).card : Int) := by
          rw [hfilter]
    _ = ∑ t ∈ Finset.range D, (if t < u then (1 : Int) else 0) := by
          exact (Finset.sum_boole (fun t => t < u) (Finset.range D)).symm

lemma int_weight_dot_eq_nat_upperLevels {n : Nat}
    (R w : Fin n → Int) (lo : Int) (u : Fin n → Nat) (D : Nat)
    (hw : ∀ i : Fin n, w i = lo + (u i : Int))
    (hD : ∀ i : Fin n, u i ≤ D) :
    (∑ i : Fin n, w i * R i)
      =
    lo * (∑ i : Fin n, R i)
      + ∑ t ∈ Finset.range D,
          ∑ i ∈ qge2UpperLevel u t, R i := by
  classical
  have hlevel_i :
      ∀ i : Fin n,
        (u i : Int) * R i
          = ∑ t ∈ Finset.range D, (if t < u i then R i else 0) := by
    intro i
    have hu := nat_eq_sum_upper_indicators (D := D) (u := u i) (hD i)
    calc
      (u i : Int) * R i
          = (∑ t ∈ Finset.range D, (if t < u i then (1 : Int) else 0))
              * R i := by rw [← hu]
      _ = ∑ t ∈ Finset.range D, (if t < u i then R i else 0) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro t _ht
          by_cases h : t < u i <;> simp [h]
  calc
    (∑ i : Fin n, w i * R i)
        = ∑ i : Fin n, (lo + (u i : Int)) * R i := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [hw i]
    _ = ∑ i : Fin n, (lo * R i + (u i : Int) * R i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
    _ = lo * (∑ i : Fin n, R i)
          + ∑ i : Fin n, (u i : Int) * R i := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ = lo * (∑ i : Fin n, R i)
          + ∑ i : Fin n,
              ∑ t ∈ Finset.range D, (if t < u i then R i else 0) := by
            congr 1
            apply Finset.sum_congr rfl
            intro i _hi
            exact hlevel_i i
    _ = lo * (∑ i : Fin n, R i)
          + ∑ t ∈ Finset.range D,
              ∑ i : Fin n, (if t < u i then R i else 0) := by
            rw [Finset.sum_comm]
    _ = lo * (∑ i : Fin n, R i)
          + ∑ t ∈ Finset.range D,
              ∑ i ∈ qge2UpperLevel u t, R i := by
            congr 1
            apply Finset.sum_congr rfl
            intro t _ht
            simp [qge2UpperLevel, Finset.sum_filter]

/--
The remaining signed-support estimate needed by the half-slack bridge.  This
is deliberately isolated from the level-set algebra: proving this goal amounts
to the sorted signed-column pattern argument.
-/
def Qge2SignedSupportHalfPenaltyGoal : Prop :=
  ∀ {n : Nat},
    Even n → 4 ≤ n →
    ∀ (c : Fin (n - 1) → Nat),
      (∀ k : Fin (n - 1), c k = 1 ∨ c k = 2) →
      ∀ (w : Fin n → Int) (lo : Int) (u : Fin n → Nat) (D : Nat),
        (∀ i : Fin n, w i = lo + (u i : Int)) →
        (∀ i : Fin n, u i ≤ D) →
        lo * (-(∑ k : Fin (n - 1), (c k : Int)))
          + ∑ t ∈ Finset.range D,
              ((∑ k : Fin (n - 1),
                  qge2ColumnCapacity n (qge2UpperLevel u t).card (c k))
                - (((n - 1 : Nat) : Int) * qge2HalfLevelPenalty n u t))
          ≤ ∑ k : Fin (n - 1), qge2SignedColumnSupport n (c k) w

def qge2SignedPatternOne (m : Nat) (j : Fin (m + m)) : Int :=
  if j.val < m - 1 then 2 else if j.val = m - 1 then 1 else -2

def qge2SignedPatternTwo (m : Nat) (j : Fin (m + m)) : Int :=
  if j.val < m - 1 then 2 else if j.val < m + 1 then -1 else -2

def qge2SignedPatternPrefixOne (m q : Nat) : Int :=
  if q ≤ m - 1 then 2 * (q : Int)
  else 4 * (m : Int) - 2 * (q : Int) - 1

def qge2SignedPatternPrefixTwo (m q : Nat) : Int :=
  if q ≤ m - 1 then 2 * (q : Int)
  else if q = m then 2 * (m : Int) - 3
  else 4 * (m : Int) - 2 * (q : Int) - 2

lemma fin_sum_if_val_lt_eq_fin_sum {n q : Nat} (hq : q ≤ n)
    (f : Fin n → Int) :
    (∑ j : Fin n, if j.val < q then f j else 0)
      = ∑ a : Fin q, f (Fin.castLE hq a) := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun j hj => ⟨j.val, by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact hj⟩)
  · intro j hj
    simp
  · intro a ha b hb hab
    exact Fin.ext (by simpa using congrArg (fun x : Fin q => x.val) hab)
  · intro a _ha
    refine ⟨Fin.castLE hq a, ?_, ?_⟩
    · simp [Fin.castLE]
    · ext
      simp [Fin.castLE]
  · intro j hj
    rfl

lemma qge2UpperLevel_sorted_prefix {n : Nat} (u : Fin n → Nat) (t : Nat) :
    ∀ j : Fin n,
      (j.val < (qge2UpperLevel u t).card) ↔
        t < u ((Tuple.sort (fun i : Fin n => -((u i : Int)))) j) := by
  classical
  let σ : Equiv.Perm (Fin n) :=
    Tuple.sort (fun i : Fin n => -((u i : Int)))
  intro j
  let f : Fin n → Int := fun j => (u (σ j) : Int)
  have hmono0 := Tuple.monotone_sort (fun i : Fin n => -((u i : Int)))
  have hmono : Monotone ((fun i : Fin n => -((u i : Int))) ∘ σ) := by
    simpa [σ] using hmono0
  have hant : Antitone f := by
    intro a b hab
    have h := hmono hab
    dsimp [Function.comp, f] at h ⊢
    omega
  have hiff :=
    Tuple.lt_card_gt_iff_apply_gt_of_antitone
      (j := j) (f := f) (a := (t : Int)) hant
  have hcard :
      (Finset.univ.filter (fun i : Fin n => (t : Int) < f i)).card
        = (qge2UpperLevel u t).card := by
    apply Finset.card_bij (fun i _hi => σ i)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      dsimp [f] at hi
      have hiNat : t < u (σ i) := by exact_mod_cast hi
      simpa [qge2UpperLevel] using hiNat
    · intro i hi j hj hσ
      exact σ.injective hσ
    · intro y hy
      refine ⟨σ.symm y, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        dsimp [f]
        have hyNat : t < u y := by
          simpa [qge2UpperLevel] using hy
        have hyInt : (t : Int) < (u y : Int) := by
          exact_mod_cast hyNat
        simpa using hyInt
      · simp
  constructor
  · intro hj
    have hj' :
        j.val < (Finset.univ.filter (fun i : Fin n => (t : Int) < f i)).card := by
      rwa [hcard]
    have h := hiff.mp hj'
    dsimp [f, σ] at h
    exact_mod_cast h
  · intro hj
    have hj' :
        j.val < (Finset.univ.filter (fun i : Fin n => (t : Int) < f i)).card := by
      apply hiff.mpr
      dsimp [f, σ]
      exact_mod_cast hj
    rwa [hcard] at hj'

lemma qge2UpperLevel_sorted_pattern_sum {n : Nat}
    (u : Fin n → Nat) (t : Nat) (pattern : Fin n → Int) :
    let σ : Equiv.Perm (Fin n) :=
      Tuple.sort (fun i : Fin n => -((u i : Int)))
    let v : Fin n → Int := fun i => pattern (σ.symm i)
    (∑ i ∈ qge2UpperLevel u t, v i)
      =
    ∑ j : Fin n,
      if j.val < (qge2UpperLevel u t).card then pattern j else 0 := by
  classical
  intro σ v
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun i _hi => σ.symm i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hiNat : t < u i := by
      simpa [qge2UpperLevel] using hi
    have hprefix :=
      (qge2UpperLevel_sorted_prefix u t (σ.symm i)).mpr
        (by simpa [σ] using hiNat)
    simpa using hprefix
  · intro i hi j hj hij
    apply σ.symm.injective at hij
    simpa using hij
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨σ j, ?_, ?_⟩
    · have hU : t < u (σ j) :=
        (qge2UpperLevel_sorted_prefix u t j).mp hj
      simpa [qge2UpperLevel] using hU
    · simp
  · intro i hi
    simp [v]

lemma sum_if_val_lt_succ {n q : Nat} (hq : q < n)
    (f : Fin n → Int) :
    (∑ j : Fin n, if j.val < q + 1 then f j else 0)
      = (∑ j : Fin n, if j.val < q then f j else 0) + f ⟨q, hq⟩ := by
  classical
  rw [fin_sum_if_val_lt_eq_fin_sum
    (n := n) (q := q + 1) (Nat.succ_le_of_lt hq)]
  rw [fin_sum_if_val_lt_eq_fin_sum (n := n) (q := q) hq.le]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.castLE]

theorem qge2SignedPatternOne_prefix_sum
    {m q : Nat} (_hm2 : 2 ≤ m) (hq : q ≤ m + m) :
    (∑ j : Fin (m + m),
      if j.val < q then qge2SignedPatternOne m j else 0)
      = qge2SignedPatternPrefixOne m q := by
  classical
  induction q with
  | zero =>
      simp [qge2SignedPatternPrefixOne]
  | succ q ih =>
      have hq_lt : q < m + m := Nat.lt_of_succ_le hq
      rw [sum_if_val_lt_succ hq_lt]
      rw [ih hq_lt.le]
      unfold qge2SignedPatternPrefixOne qge2SignedPatternOne
      by_cases hsucc : q + 1 ≤ m - 1
      · have hqle : q ≤ m - 1 := by omega
        have hq_lt_m1 : q < m - 1 := by omega
        simp [hsucc, hqle, hq_lt_m1]
        ring_nf
      · by_cases hqle : q ≤ m - 1
        · have hqeq : q = m - 1 := by omega
          subst q
          simp only [Std.le_refl, ↓reduceIte, lt_self_iff_false,
            add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero,
            Nat.cast_add, Nat.cast_one]
          have hcast : ((m - 1 : Nat) : Int) = (m : Int) - 1 := by
            omega
          rw [hcast]
          ring
        · have hnot1 : ¬ q < m - 1 := by omega
          have hnot2 : ¬ q = m - 1 := by omega
          simp [hsucc, hqle, hnot1, hnot2]
          ring

theorem qge2SignedPatternTwo_prefix_sum
    {m q : Nat} (_hm2 : 2 ≤ m) (hq : q ≤ m + m) :
    (∑ j : Fin (m + m),
      if j.val < q then qge2SignedPatternTwo m j else 0)
      = qge2SignedPatternPrefixTwo m q := by
  classical
  induction q with
  | zero =>
      simp [qge2SignedPatternPrefixTwo]
  | succ q ih =>
      have hq_lt : q < m + m := Nat.lt_of_succ_le hq
      rw [sum_if_val_lt_succ hq_lt]
      rw [ih hq_lt.le]
      unfold qge2SignedPatternPrefixTwo qge2SignedPatternTwo
      by_cases hsucc : q + 1 ≤ m - 1
      · have hqle : q ≤ m - 1 := by omega
        have hq_lt_m1 : q < m - 1 := by omega
        simp [hsucc, hqle, hq_lt_m1]
        ring_nf
      · by_cases hqle : q ≤ m - 1
        · have hqeq : q = m - 1 := by omega
          subst q
          have hsucc_eq : m - 1 + 1 = m := by omega
          have hnotle : ¬ m ≤ m - 1 := by omega
          simp only [hsucc_eq, hnotle, Std.le_refl, ↓reduceIte,
            lt_self_iff_false, Order.lt_add_one_iff, tsub_le_iff_right,
            le_add_iff_nonneg_right, zero_le, Int.reduceNeg]
          have hcast : ((m - 1 : Nat) : Int) = (m : Int) - 1 := by
            omega
          rw [hcast]
          ring
        · by_cases hqeqm : q = m
          · subst q
            have hnotle : ¬ m ≤ m - 1 := by omega
            have hnotlt : ¬ m < m - 1 := by omega
            simp [hnotle, hnotlt]
            ring
          · have hsucc_ne_m : ¬ q + 1 = m := by omega
            have hnotlt : ¬ q < m - 1 := by omega
            have hnotlt2 : ¬ q < m + 1 := by omega
            simp [hsucc, hqle, hqeqm, hsucc_ne_m, hnotlt, hnotlt2]
            ring

theorem qge2SignedPatternPrefixOne_capacity
    {m q : Nat} (_hm2 : 2 ≤ m) (hq : q ≤ m + m) :
    qge2ColumnCapacity (m + m) q 1
      ≤ qge2SignedPatternPrefixOne m q := by
  unfold qge2SignedPatternPrefixOne qge2ColumnCapacity
  by_cases h : q ≤ m - 1
  · simp [h]
  · simp [h]
    omega

theorem qge2SignedPatternPrefixTwo_capacity_sub_half
    {m q : Nat} (_hm2 : 2 ≤ m) (hq : q ≤ m + m) :
    qge2ColumnCapacity (m + m) q 2
        - (if q = m then 1 else 0 : Int)
      ≤ qge2SignedPatternPrefixTwo m q := by
  unfold qge2SignedPatternPrefixTwo qge2ColumnCapacity
  by_cases h : q ≤ m - 1
  · simp [h]
    omega
  · simp [h]
    by_cases hqeq : q = m <;> simp [hqeq] <;> omega

theorem qge2SignedPatternOne_isSigned {m : Nat} (j : Fin (m + m)) :
    IsSignedVal (qge2SignedPatternOne m j) := by
  unfold qge2SignedPatternOne
  by_cases hlt : j.val < m - 1
  · simp [hlt, IsSignedVal, signedVals]
  · by_cases heq : j.val = m - 1
    · simp [heq, IsSignedVal, signedVals]
    · simp [hlt, heq, IsSignedVal, signedVals]

theorem qge2SignedPatternTwo_isSigned {m : Nat} (j : Fin (m + m)) :
    IsSignedVal (qge2SignedPatternTwo m j) := by
  unfold qge2SignedPatternTwo
  by_cases hlt : j.val < m - 1
  · simp [hlt, IsSignedVal, signedVals]
  · by_cases hmid : j.val < m + 1
    · simp [hlt, hmid, IsSignedVal, signedVals]
    · simp [hlt, hmid, IsSignedVal, signedVals]

theorem qge2SignedPatternOne_sum {m : Nat} (hm2 : 2 ≤ m) :
    (∑ j : Fin (m + m), qge2SignedPatternOne m j) = -1 := by
  have hprefix :=
    qge2SignedPatternOne_prefix_sum (m := m) (q := m + m) hm2 le_rfl
  have hleft :
      (∑ j : Fin (m + m),
        if j.val < m + m then qge2SignedPatternOne m j else 0)
        = ∑ j : Fin (m + m), qge2SignedPatternOne m j := by
    apply Finset.sum_congr rfl
    intro j _hj
    simp [j.isLt]
  have hright : qge2SignedPatternPrefixOne m (m + m) = -1 := by
    unfold qge2SignedPatternPrefixOne
    have hnot : ¬ m + m ≤ m - 1 := by omega
    simp [hnot]
    omega
  rw [← hleft, hprefix, hright]

theorem qge2SignedPatternTwo_sum {m : Nat} (hm2 : 2 ≤ m) :
    (∑ j : Fin (m + m), qge2SignedPatternTwo m j) = -2 := by
  have hprefix :=
    qge2SignedPatternTwo_prefix_sum (m := m) (q := m + m) hm2 le_rfl
  have hleft :
      (∑ j : Fin (m + m),
        if j.val < m + m then qge2SignedPatternTwo m j else 0)
        = ∑ j : Fin (m + m), qge2SignedPatternTwo m j := by
    apply Finset.sum_congr rfl
    intro j _hj
    simp [j.isLt]
  have hright : qge2SignedPatternPrefixTwo m (m + m) = -2 := by
    unfold qge2SignedPatternPrefixTwo
    have hnot : ¬ m + m ≤ m - 1 := by omega
    have hne : ¬ m + m = m := by omega
    simp [hnot]
    omega
  rw [← hleft, hprefix, hright]

theorem qge2SignedColumnSupport_one_ge_levelCapacity_sub_halfPenalty
    {m : Nat} (hm2 : 2 ≤ m)
    (w : Fin (m + m) → Int) (lo : Int) (u : Fin (m + m) → Nat) (D : Nat)
    (hw : ∀ i : Fin (m + m), w i = lo + (u i : Int))
    (hD : ∀ i : Fin (m + m), u i ≤ D) :
    lo * (-1)
      + ∑ t ∈ Finset.range D,
          (qge2ColumnCapacity (m + m) (qge2UpperLevel u t).card 1
            - qge2HalfLevelPenalty (m + m) u t)
      ≤ qge2SignedColumnSupport (m + m) 1 w := by
  classical
  let σ : Equiv.Perm (Fin (m + m)) :=
    Tuple.sort (fun i : Fin (m + m) => -((u i : Int)))
  let v : Fin (m + m) → Int :=
    fun i => qge2SignedPatternOne m (σ.symm i)
  have hv : ∀ i : Fin (m + m), IsSignedVal (v i) := by
    intro i
    exact qge2SignedPatternOne_isSigned (m := m) (σ.symm i)
  have hsumv : (∑ i : Fin (m + m), v i) = -1 := by
    calc
      (∑ i : Fin (m + m), v i)
          = ∑ j : Fin (m + m), qge2SignedPatternOne m j := by
            simpa [v] using
              (Equiv.sum_comp σ.symm (fun j : Fin (m + m) =>
                qge2SignedPatternOne m j))
      _ = -1 := qge2SignedPatternOne_sum hm2
  have hsupport :
      (∑ i : Fin (m + m), w i * v i)
        ≤ qge2SignedColumnSupport (m + m) 1 w :=
    qge2SignedColumnSupport_ge_of_intColumn
      (n := m + m) (c := 1) w hv hsumv
  have hdot :
      (∑ i : Fin (m + m), w i * v i)
        =
      lo * (∑ i : Fin (m + m), v i)
        + ∑ t ∈ Finset.range D,
            ∑ i ∈ qge2UpperLevel u t, v i :=
    int_weight_dot_eq_nat_upperLevels v w lo u D hw hD
  have hlevel :
      ∀ t ∈ Finset.range D,
        qge2ColumnCapacity (m + m) (qge2UpperLevel u t).card 1
            - qge2HalfLevelPenalty (m + m) u t
          ≤ ∑ i ∈ qge2UpperLevel u t, v i := by
    intro t _ht
    let q : Nat := (qge2UpperLevel u t).card
    have hq : q ≤ m + m := by
      dsimp [q]
      simpa [Fintype.card_fin] using
        (Finset.card_le_univ (s := qge2UpperLevel u t))
    have hpen_nonneg : 0 ≤ qge2HalfLevelPenalty (m + m) u t := by
      unfold qge2HalfLevelPenalty
      by_cases h : (qge2UpperLevel u t).card = (m + m) / 2 <;> simp [h]
    have hcap :
        qge2ColumnCapacity (m + m) q 1
          ≤ qge2SignedPatternPrefixOne m q :=
      qge2SignedPatternPrefixOne_capacity (m := m) (q := q) hm2 hq
    have hprefix :
        (∑ j : Fin (m + m),
          if j.val < q then qge2SignedPatternOne m j else 0)
          = qge2SignedPatternPrefixOne m q :=
      qge2SignedPatternOne_prefix_sum (m := m) (q := q) hm2 hq
    have hsorted :
        (∑ i ∈ qge2UpperLevel u t, v i)
          =
        ∑ j : Fin (m + m),
          if j.val < q then qge2SignedPatternOne m j else 0 := by
      have h :=
        qge2UpperLevel_sorted_pattern_sum
          (n := m + m) u t (qge2SignedPatternOne m)
      simpa [q, σ, v] using h
    calc
      qge2ColumnCapacity (m + m) (qge2UpperLevel u t).card 1
          - qge2HalfLevelPenalty (m + m) u t
          ≤ qge2ColumnCapacity (m + m) q 1 := by
            dsimp [q]
            nlinarith
      _ ≤ qge2SignedPatternPrefixOne m q := hcap
      _ = ∑ j : Fin (m + m),
            if j.val < q then qge2SignedPatternOne m j else 0 := hprefix.symm
      _ = ∑ i ∈ qge2UpperLevel u t, v i := hsorted.symm
  calc
    lo * (-1)
      + ∑ t ∈ Finset.range D,
          (qge2ColumnCapacity (m + m) (qge2UpperLevel u t).card 1
            - qge2HalfLevelPenalty (m + m) u t)
        ≤ lo * (∑ i : Fin (m + m), v i)
            + ∑ t ∈ Finset.range D,
                ∑ i ∈ qge2UpperLevel u t, v i := by
          have hsum :
              (∑ t ∈ Finset.range D,
                (qge2ColumnCapacity (m + m) (qge2UpperLevel u t).card 1
                  - qge2HalfLevelPenalty (m + m) u t))
                ≤ ∑ t ∈ Finset.range D,
                    ∑ i ∈ qge2UpperLevel u t, v i := by
            apply Finset.sum_le_sum
            intro t ht
            exact hlevel t ht
          simpa [hsumv] using add_le_add_left hsum (lo * (-1))
    _ = ∑ i : Fin (m + m), w i * v i := by
          rw [← hdot]
    _ ≤ qge2SignedColumnSupport (m + m) 1 w := hsupport

theorem qge2SignedColumnSupport_two_ge_levelCapacity_sub_halfPenalty
    {m : Nat} (hm2 : 2 ≤ m)
    (w : Fin (m + m) → Int) (lo : Int) (u : Fin (m + m) → Nat) (D : Nat)
    (hw : ∀ i : Fin (m + m), w i = lo + (u i : Int))
    (hD : ∀ i : Fin (m + m), u i ≤ D) :
    lo * (-2)
      + ∑ t ∈ Finset.range D,
          (qge2ColumnCapacity (m + m) (qge2UpperLevel u t).card 2
            - qge2HalfLevelPenalty (m + m) u t)
      ≤ qge2SignedColumnSupport (m + m) 2 w := by
  classical
  let σ : Equiv.Perm (Fin (m + m)) :=
    Tuple.sort (fun i : Fin (m + m) => -((u i : Int)))
  let v : Fin (m + m) → Int :=
    fun i => qge2SignedPatternTwo m (σ.symm i)
  have hv : ∀ i : Fin (m + m), IsSignedVal (v i) := by
    intro i
    exact qge2SignedPatternTwo_isSigned (m := m) (σ.symm i)
  have hsumv : (∑ i : Fin (m + m), v i) = -2 := by
    calc
      (∑ i : Fin (m + m), v i)
          = ∑ j : Fin (m + m), qge2SignedPatternTwo m j := by
            simpa [v] using
              (Equiv.sum_comp σ.symm (fun j : Fin (m + m) =>
                qge2SignedPatternTwo m j))
      _ = -2 := qge2SignedPatternTwo_sum hm2
  have hsupport :
      (∑ i : Fin (m + m), w i * v i)
        ≤ qge2SignedColumnSupport (m + m) 2 w :=
    qge2SignedColumnSupport_ge_of_intColumn
      (n := m + m) (c := 2) w hv hsumv
  have hdot :
      (∑ i : Fin (m + m), w i * v i)
        =
      lo * (∑ i : Fin (m + m), v i)
        + ∑ t ∈ Finset.range D,
            ∑ i ∈ qge2UpperLevel u t, v i :=
    int_weight_dot_eq_nat_upperLevels v w lo u D hw hD
  have hlevel :
      ∀ t ∈ Finset.range D,
        qge2ColumnCapacity (m + m) (qge2UpperLevel u t).card 2
            - qge2HalfLevelPenalty (m + m) u t
          ≤ ∑ i ∈ qge2UpperLevel u t, v i := by
    intro t _ht
    let q : Nat := (qge2UpperLevel u t).card
    have hq : q ≤ m + m := by
      dsimp [q]
      simpa [Fintype.card_fin] using
        (Finset.card_le_univ (s := qge2UpperLevel u t))
    have hpen :
        qge2HalfLevelPenalty (m + m) u t
          = (if q = m then 1 else 0 : Int) := by
      have hdiv : (m + m) / 2 = m := by omega
      simp [qge2HalfLevelPenalty, q, hdiv]
    have hcap :
        qge2ColumnCapacity (m + m) q 2
            - (if q = m then 1 else 0 : Int)
          ≤ qge2SignedPatternPrefixTwo m q :=
      qge2SignedPatternPrefixTwo_capacity_sub_half (m := m) (q := q) hm2 hq
    have hprefix :
        (∑ j : Fin (m + m),
          if j.val < q then qge2SignedPatternTwo m j else 0)
          = qge2SignedPatternPrefixTwo m q :=
      qge2SignedPatternTwo_prefix_sum (m := m) (q := q) hm2 hq
    have hsorted :
        (∑ i ∈ qge2UpperLevel u t, v i)
          =
        ∑ j : Fin (m + m),
          if j.val < q then qge2SignedPatternTwo m j else 0 := by
      have h :=
        qge2UpperLevel_sorted_pattern_sum
          (n := m + m) u t (qge2SignedPatternTwo m)
      simpa [q, σ, v] using h
    calc
      qge2ColumnCapacity (m + m) (qge2UpperLevel u t).card 2
          - qge2HalfLevelPenalty (m + m) u t
          = qge2ColumnCapacity (m + m) q 2
              - (if q = m then 1 else 0 : Int) := by
            simp [q, hpen]
      _ ≤ qge2SignedPatternPrefixTwo m q := hcap
      _ = ∑ j : Fin (m + m),
            if j.val < q then qge2SignedPatternTwo m j else 0 := hprefix.symm
      _ = ∑ i ∈ qge2UpperLevel u t, v i := hsorted.symm
  calc
    lo * (-2)
      + ∑ t ∈ Finset.range D,
          (qge2ColumnCapacity (m + m) (qge2UpperLevel u t).card 2
            - qge2HalfLevelPenalty (m + m) u t)
        ≤ lo * (∑ i : Fin (m + m), v i)
            + ∑ t ∈ Finset.range D,
                ∑ i ∈ qge2UpperLevel u t, v i := by
          have hsum :
              (∑ t ∈ Finset.range D,
                (qge2ColumnCapacity (m + m) (qge2UpperLevel u t).card 2
                  - qge2HalfLevelPenalty (m + m) u t))
                ≤ ∑ t ∈ Finset.range D,
                    ∑ i ∈ qge2UpperLevel u t, v i := by
            apply Finset.sum_le_sum
            intro t ht
            exact hlevel t ht
          simpa [hsumv] using add_le_add_left hsum (lo * (-2))
    _ = ∑ i : Fin (m + m), w i * v i := by
          rw [← hdot]
    _ ≤ qge2SignedColumnSupport (m + m) 2 w := hsupport

theorem qge2SignedSupportHalfPenaltyGoal :
    Qge2SignedSupportHalfPenaltyGoal := by
  classical
  intro n hnEven hn4 c hc w lo u D hw hD
  rcases hnEven with ⟨m, rfl⟩
  have hm2 : 2 ≤ m := by omega
  have hcol :
      ∀ k : Fin (m + m - 1),
        lo * (-(c k : Int))
          + ∑ t ∈ Finset.range D,
              (qge2ColumnCapacity (m + m) (qge2UpperLevel u t).card (c k)
                - qge2HalfLevelPenalty (m + m) u t)
          ≤ qge2SignedColumnSupport (m + m) (c k) w := by
    intro k
    rcases hc k with hck | hck
    · rw [hck]
      exact qge2SignedColumnSupport_one_ge_levelCapacity_sub_halfPenalty
        hm2 w lo u D hw hD
    · rw [hck]
      exact qge2SignedColumnSupport_two_ge_levelCapacity_sub_halfPenalty
        hm2 w lo u D hw hD
  have hsum :
      (∑ k : Fin (m + m - 1),
        (lo * (-(c k : Int))
          + ∑ t ∈ Finset.range D,
              (qge2ColumnCapacity (m + m) (qge2UpperLevel u t).card (c k)
                - qge2HalfLevelPenalty (m + m) u t)))
        ≤ ∑ k : Fin (m + m - 1),
            qge2SignedColumnSupport (m + m) (c k) w := by
    apply Finset.sum_le_sum
    intro k _hk
    exact hcol k
  have hleft :
      (∑ k : Fin (m + m - 1),
        (lo * (-(c k : Int))
          + ∑ t ∈ Finset.range D,
              (qge2ColumnCapacity (m + m) (qge2UpperLevel u t).card (c k)
                - qge2HalfLevelPenalty (m + m) u t)))
        =
      lo * (-(∑ k : Fin (m + m - 1), (c k : Int)))
        + ∑ t ∈ Finset.range D,
            ((∑ k : Fin (m + m - 1),
                qge2ColumnCapacity (m + m) (qge2UpperLevel u t).card (c k))
              - (((m + m - 1 : Nat) : Int)
                  * qge2HalfLevelPenalty (m + m) u t)) := by
    calc
      (∑ k : Fin (m + m - 1),
        (lo * (-(c k : Int))
          + ∑ t ∈ Finset.range D,
              (qge2ColumnCapacity (m + m) (qge2UpperLevel u t).card (c k)
                - qge2HalfLevelPenalty (m + m) u t)))
          =
        (∑ k : Fin (m + m - 1), lo * (-(c k : Int)))
          + ∑ k : Fin (m + m - 1),
              ∑ t ∈ Finset.range D,
                (qge2ColumnCapacity (m + m) (qge2UpperLevel u t).card (c k)
                  - qge2HalfLevelPenalty (m + m) u t) := by
            rw [Finset.sum_add_distrib]
      _ =
        lo * (-(∑ k : Fin (m + m - 1), (c k : Int)))
          + ∑ t ∈ Finset.range D,
              ∑ k : Fin (m + m - 1),
                (qge2ColumnCapacity (m + m) (qge2UpperLevel u t).card (c k)
                  - qge2HalfLevelPenalty (m + m) u t) := by
            rw [← Finset.mul_sum, Finset.sum_neg_distrib]
            rw [Finset.sum_comm]
      _ =
        lo * (-(∑ k : Fin (m + m - 1), (c k : Int)))
          + ∑ t ∈ Finset.range D,
              ((∑ k : Fin (m + m - 1),
                  qge2ColumnCapacity (m + m) (qge2UpperLevel u t).card (c k))
                - (((m + m - 1 : Nat) : Int)
                    * qge2HalfLevelPenalty (m + m) u t)) := by
            congr 1
            apply Finset.sum_congr rfl
            intro t _ht
            simp [Finset.sum_sub_distrib, Finset.sum_const, Fintype.card_fin]
  rw [← hleft]
  exact hsum

theorem qge2IndicatorCutsHalfSlackToSupportGoal_of_signedSupportHalfPenalty
    (hSupport : Qge2SignedSupportHalfPenaltyGoal) :
    Qge2IndicatorCutsHalfSlackToSupportGoal := by
  classical
  intro n hnEven hn4 c hc R hTotal hCuts hHalf w
  rcases exists_nat_shift_of_int_weight w with ⟨lo, u, D, hw, hD⟩
  have hLeft :
      (∑ i : Fin n, w i * R i)
        =
      lo * (∑ i : Fin n, R i)
        + ∑ t ∈ Finset.range D,
            ∑ i ∈ qge2UpperLevel u t, R i :=
    int_weight_dot_eq_nat_upperLevels R w lo u D hw hD
  have hLevels :
      ∀ t ∈ Finset.range D,
        (∑ i ∈ qge2UpperLevel u t, R i)
          ≤
        (∑ k : Fin (n - 1),
            qge2ColumnCapacity n (qge2UpperLevel u t).card (c k))
          - (((n - 1 : Nat) : Int) * qge2HalfLevelPenalty n u t) := by
    intro t _ht
    by_cases hmid : (qge2UpperLevel u t).card = n / 2
    · have h := hHalf (qge2UpperLevel u t) hmid
      simpa [qge2HalfLevelPenalty, hmid] using h
    · have h := hCuts (qge2UpperLevel u t)
      have hpen : qge2HalfLevelPenalty n u t = 0 := by
        simp [qge2HalfLevelPenalty, hmid]
      simpa [hpen] using h
  calc
    (∑ i : Fin n, w i * R i)
        = lo * (∑ i : Fin n, R i)
            + ∑ t ∈ Finset.range D,
                ∑ i ∈ qge2UpperLevel u t, R i := hLeft
    _ = lo * (-(∑ k : Fin (n - 1), (c k : Int)))
            + ∑ t ∈ Finset.range D,
                ∑ i ∈ qge2UpperLevel u t, R i := by
          rw [hTotal]
    _ ≤ lo * (-(∑ k : Fin (n - 1), (c k : Int)))
            + ∑ t ∈ Finset.range D,
                ((∑ k : Fin (n - 1),
                    qge2ColumnCapacity n (qge2UpperLevel u t).card (c k))
                  - (((n - 1 : Nat) : Int) * qge2HalfLevelPenalty n u t)) := by
          have hsum :
              (∑ t ∈ Finset.range D,
                ∑ i ∈ qge2UpperLevel u t, R i)
                ≤ ∑ t ∈ Finset.range D,
                    ((∑ k : Fin (n - 1),
                        qge2ColumnCapacity n (qge2UpperLevel u t).card (c k))
                      - (((n - 1 : Nat) : Int) * qge2HalfLevelPenalty n u t)) := by
            apply Finset.sum_le_sum
            intro t ht
            exact hLevels t ht
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hsum (lo * (-(∑ k : Fin (n - 1), (c k : Int))))
    _ ≤ ∑ k : Fin (n - 1), qge2SignedColumnSupport n (c k) w :=
          hSupport hnEven hn4 c hc w lo u D hw hD

theorem qge2IndicatorCutsHalfSlackToSupportGoal :
    Qge2IndicatorCutsHalfSlackToSupportGoal :=
  qge2IndicatorCutsHalfSlackToSupportGoal_of_signedSupportHalfPenalty
    qge2SignedSupportHalfPenaltyGoal

theorem qge2ColumnCapacity_half_ge_sub_two {n c : Nat}
    (hnEven : Even n) (hn4 : 4 ≤ n) (hc : c = 1 ∨ c = 2) :
    (((n - 2 : Nat) : Int) ≤ qge2ColumnCapacity n (n / 2) c) := by
  rcases hnEven with ⟨m, rfl⟩
  have hm2 : 2 ≤ m := by omega
  have hdiv : (m + m) / 2 = m := by omega
  have hsub : m + m - m = m := by omega
  rw [qge2ColumnCapacity]
  rw [hdiv, hsub]
  apply le_min
  · omega
  · rcases hc with rfl | rfl <;> omega

theorem qge2OrdinaryRowTarget_sum_le_card_mul_sub_eps
    {n r : Nat} (a epsBit : Fin n → Nat)
    (ha : ∀ i : Fin n, a i = 1 ∨ a i = 2)
    (J : Finset (Fin n)) :
    (∑ i ∈ J, qge2OrdinaryRowTarget n r a epsBit i)
      ≤ (J.card : Int) * ((r : Int) - 1)
          - (n : Int) * (∑ i ∈ J, (epsBit i : Int)) := by
  classical
  calc
    (∑ i ∈ J, qge2OrdinaryRowTarget n r a epsBit i)
        ≤ ∑ i ∈ J, ((r : Int) - 1 - (n : Int) * (epsBit i : Int)) := by
          apply Finset.sum_le_sum
          intro i _hi
          have hai : 1 ≤ (a i : Int) := by
            rcases ha i with h | h <;> simp [h]
          simp [qge2OrdinaryRowTarget]
          nlinarith
    _ = (J.card : Int) * ((r : Int) - 1)
          - (n : Int) * (∑ i ∈ J, (epsBit i : Int)) := by
          simp [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const]
          ring

theorem qge2_eps_sum_on_half_ge_sub
    {n r : Nat} (hnEven : Even n)
    (epsBit : Fin n → Nat)
    (heps : ∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1)
    (hepsSum : (∑ i : Fin n, epsBit i) = r)
    (J : Finset (Fin n)) (hJ : J.card = n / 2)
    (hrgt : n / 2 < r) :
    r - n / 2 ≤ ∑ i ∈ J, epsBit i := by
  classical
  have hcompl_card :
      Jᶜ.card = n / 2 := by
    have hcard : Jᶜ.card = n - J.card := by
      simpa [Fintype.card_fin] using Finset.card_compl J
    rw [hcard, hJ]
    rcases hnEven with ⟨m, rfl⟩
    omega
  have hcompl_le :
      (∑ i ∈ Jᶜ, epsBit i) ≤ n / 2 := by
    calc
      (∑ i ∈ Jᶜ, epsBit i) ≤ ∑ _i ∈ Jᶜ, 1 := by
        apply Finset.sum_le_sum
        intro i _hi
        rcases heps i with h | h <;> simp [h]
      _ = n / 2 := by
        simp [hcompl_card]
  have hsplit :
      (∑ i : Fin n, epsBit i)
        = (∑ i ∈ J, epsBit i) + ∑ i ∈ Jᶜ, epsBit i := by
    rw [← Finset.sum_union]
    · simp
    · exact disjoint_compl_right
  have hr_eq :
      r = (∑ i ∈ J, epsBit i) + ∑ i ∈ Jᶜ, epsBit i := by
    rw [← hepsSum, hsplit]
  omega

theorem qge2OrdinaryRowTarget_half_sum_le_half_product
    {n r : Nat} (hnEven : Even n) (hn4 : 4 ≤ n)
    (hrlt : r < n) (_hrpos : 0 < r)
    (a epsBit : Fin n → Nat)
    (ha : ∀ i : Fin n, a i = 1 ∨ a i = 2)
    (heps : ∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1)
    (hepsSum : (∑ i : Fin n, epsBit i) = r)
    (J : Finset (Fin n)) (hJ : J.card = n / 2) :
    (∑ i ∈ J, qge2OrdinaryRowTarget n r a epsBit i)
      ≤ ((n / 2 : Nat) : Int) * (((n / 2 : Nat) : Int) - 1) := by
  classical
  rcases hnEven with ⟨m, rfl⟩
  have hm2 : 2 ≤ m := by omega
  have hJm : J.card = m := by
    have hdiv : (m + m) / 2 = m := by omega
    simpa [hdiv] using hJ
  let EJ : Nat := ∑ i ∈ J, epsBit i
  have hbound :
      (∑ i ∈ J, qge2OrdinaryRowTarget (m + m) r a epsBit i)
        ≤ (m : Int) * ((r : Int) - 1) - (2 * (m : Int)) * (EJ : Int) := by
    have h := qge2OrdinaryRowTarget_sum_le_card_mul_sub_eps
      (n := m + m) (r := r) a epsBit ha J
    have hcast : ((m + m : Nat) : Int) = 2 * (m : Int) := by omega
    simpa [EJ, hJm, hcast, mul_assoc, mul_comm, mul_left_comm] using h
  by_cases hrle : r ≤ m
  · have hmain :
        (m : Int) * ((r : Int) - 1) - (2 * (m : Int)) * (EJ : Int)
          ≤ (m : Int) * ((m : Int) - 1) := by
      have hEJ : 0 ≤ (EJ : Int) := by omega
      nlinarith
    have hgoal := le_trans hbound hmain
    have hdiv : (m + m) / 2 = m := by omega
    simpa [hdiv] using hgoal
  · have hrgt : m < r := Nat.lt_of_not_ge hrle
    have hEJ_ge_nat : r - m ≤ EJ := by
      have hdiv : (m + m) / 2 = m := by omega
      have htmp := qge2_eps_sum_on_half_ge_sub
        (n := m + m) (r := r) ⟨m, rfl⟩
        epsBit heps hepsSum J hJ (by simpa [hdiv] using hrgt)
      simpa [EJ, hdiv] using htmp
    have hmain :
        (m : Int) * ((r : Int) - 1) - (2 * (m : Int)) * (EJ : Int)
          ≤ (m : Int) * ((m : Int) - 1) := by
      have hEJ_ge : (r : Int) - (m : Int) ≤ (EJ : Int) := by
        have hcast : ((r - m : Nat) : Int) = (r : Int) - (m : Int) := by
          omega
        rw [← hcast]
        exact_mod_cast hEJ_ge_nat
      nlinarith
    have hgoal := le_trans hbound hmain
    have hdiv : (m + m) / 2 = m := by omega
    simpa [hdiv] using hgoal

theorem qge2ColumnCapacity_half_sum_sub_allColumns_ge_half_product
    {n : Nat} (hnEven : Even n) (hn4 : 4 ≤ n)
    (c : Fin (n - 1) → Nat)
    (hc : ∀ k : Fin (n - 1), c k = 1 ∨ c k = 2) :
    ((n / 2 : Nat) : Int) * (((n / 2 : Nat) : Int) - 1)
      ≤ (∑ k : Fin (n - 1), qge2ColumnCapacity n (n / 2) (c k))
          - ((n - 1 : Nat) : Int) := by
  classical
  rcases hnEven with ⟨m, rfl⟩
  have hm2 : 2 ≤ m := by omega
  have hcapEach :
      ∀ k : Fin (m + m - 1),
        (((m + m - 2 : Nat) : Int)
          ≤ qge2ColumnCapacity (m + m) ((m + m) / 2) (c k)) := by
    intro k
    exact qge2ColumnCapacity_half_ge_sub_two (n := m + m) (c := c k)
      ⟨m, rfl⟩ hn4 (hc k)
  have hsum_ge :
      (∑ _k : Fin (m + m - 1), ((m + m - 2 : Nat) : Int))
        ≤ ∑ k : Fin (m + m - 1),
            qge2ColumnCapacity (m + m) ((m + m) / 2) (c k) := by
    apply Finset.sum_le_sum
    intro k _hk
    exact hcapEach k
  have hsum_ge' :
      ((m + m - 1 : Nat) : Int) * ((m + m - 2 : Nat) : Int)
        ≤ ∑ k : Fin (m + m - 1),
            qge2ColumnCapacity (m + m) ((m + m) / 2) (c k) := by
    simpa [Finset.sum_const, Fintype.card_fin, mul_comm] using hsum_ge
  have hcast1 : ((m + m - 1 : Nat) : Int) = 2 * (m : Int) - 1 := by omega
  have hcast2 : ((m + m - 2 : Nat) : Int) = 2 * (m : Int) - 2 := by omega
  have hcastm : (((m + m) / 2 : Nat) : Int) = (m : Int) := by
    have hdiv : (m + m) / 2 = m := by omega
    exact_mod_cast hdiv
  have htarget :
      (m : Int) * ((m : Int) - 1)
        ≤ ((m + m - 1 : Nat) : Int) * ((m + m - 2 : Nat) : Int)
            - ((m + m - 1 : Nat) : Int) := by
    rw [hcast1, hcast2]
    nlinarith
  calc
    (((m + m) / 2 : Nat) : Int) * ((((m + m) / 2 : Nat) : Int) - 1)
        = (m : Int) * ((m : Int) - 1) := by rw [hcastm]
    _ ≤ ((m + m - 1 : Nat) : Int) * ((m + m - 2 : Nat) : Int)
          - ((m + m - 1 : Nat) : Int) := htarget
    _ ≤ (∑ k : Fin (m + m - 1),
            qge2ColumnCapacity (m + m) ((m + m) / 2) (c k))
          - ((m + m - 1 : Nat) : Int) := by
          nlinarith

theorem qge2OrdinaryRowTarget_halfLevel_le_capacity_sub_allColumns
    {n r : Nat} (hnEven : Even n) (hn4 : 4 ≤ n)
    (hrlt : r < n) (hrpos : 0 < r)
    (a epsBit : Fin n → Nat) (c : Fin (n - 1) → Nat)
    (ha : ∀ i : Fin n, a i = 1 ∨ a i = 2)
    (heps : ∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1)
    (hc : ∀ k : Fin (n - 1), c k = 1 ∨ c k = 2)
    (hepsSum : (∑ i : Fin n, epsBit i) = r)
    (J : Finset (Fin n)) (hJ : J.card = n / 2) :
    (∑ i ∈ J, qge2OrdinaryRowTarget n r a epsBit i)
      ≤ (∑ k : Fin (n - 1), qge2ColumnCapacity n J.card (c k))
          - ((n - 1 : Nat) : Int) := by
  have hrow :=
    qge2OrdinaryRowTarget_half_sum_le_half_product
      hnEven hn4 hrlt hrpos a epsBit ha heps hepsSum J hJ
  have hcap :=
    qge2ColumnCapacity_half_sum_sub_allColumns_ge_half_product
      hnEven hn4 c hc
  rw [hJ]
  exact le_trans hrow hcap

theorem qge2OrdinaryHalfSlackGoal :
    Qge2OrdinaryHalfSlackGoal := by
  intro n r hnEven hn4 hrlt hrpos a epsBit c ha heps hc hepsSum J hJ
  exact qge2OrdinaryRowTarget_halfLevel_le_capacity_sub_allColumns
    hnEven hn4 hrlt hrpos a epsBit c ha heps hc hepsSum J hJ

theorem ordinaryQge2IndicatorToFullSupportGoal_of_signedSupportHalfPenalty
    (hSupport : Qge2SignedSupportHalfPenaltyGoal) :
    OrdinaryQge2IndicatorToFullSupportGoal :=
  ordinaryQge2IndicatorToFullSupportGoal_of_halfSlackBridge
    (qge2IndicatorCutsHalfSlackToSupportGoal_of_signedSupportHalfPenalty hSupport)
    qge2OrdinaryHalfSlackGoal

theorem ordinaryQge2IndicatorToFullSupportGoal_of_internalHalfSlack :
    OrdinaryQge2IndicatorToFullSupportGoal :=
  ordinaryQge2IndicatorToFullSupportGoal_of_signedSupportHalfPenalty
    qge2SignedSupportHalfPenaltyGoal

theorem indicator_weight_sum {n : Nat} (J : Finset (Fin n))
    (R : Fin n → Int) :
    (∑ i : Fin n, (if i ∈ J then (1 : Int) else 0) * R i)
      = ∑ i ∈ J, R i := by
  classical
  calc
    (∑ i : Fin n, (if i ∈ J then (1 : Int) else 0) * R i)
        = ∑ i : Fin n, if i ∈ J then R i else 0 := by
            apply Finset.sum_congr rfl
            intro i _hi
            by_cases h : i ∈ J <;> simp [h]
    _ = ∑ i ∈ J, R i := by
          simp

theorem qge2SignedColumnSupport_indicator_le_capacity
    {n c : Nat} (hnEven : Even n) (hn4 : 4 ≤ n)
    (hc : c = 1 ∨ c = 2) (J : Finset (Fin n)) :
    qge2SignedColumnSupport n c
        (fun i : Fin n => if i ∈ J then (1 : Int) else 0)
      ≤ qge2ColumnCapacity n J.card c := by
  classical
  let w : Fin n → Int := fun i => if i ∈ J then (1 : Int) else 0
  let vals : Finset Int :=
    (qge2SignedColumnFinset n c).image
      (fun x : Fin n → SignedValInt =>
        ∑ i ∈ J, SignedValInt.toInt (x i))
  have hvals_bound :
      ∀ z ∈ vals, z ≤ qge2ColumnCapacity n J.card c := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    exact
      qge2ColumnCapacity_upper_bound
        (v := fun i : Fin n => SignedValInt.toInt (x i))
        (fun i => SignedValInt.isSignedVal (x i))
        (qge2SignedColumnFinset_sum hx) J
  have hvals_nonempty : vals.Nonempty := by
    rcases hnEven with ⟨m, rfl⟩
    have hm2 : 2 ≤ m := by omega
    rcases hc with rfl | rfl
    · let x : Fin (m + m) → SignedValInt :=
        fun i => SignedValInt.ofInt
          (qge2SignedPatternOne m i)
          (qge2SignedPatternOne_isSigned (m := m) i)
      have hx : x ∈ qge2SignedColumnFinset (m + m) 1 := by
        simp [qge2SignedColumnFinset, x, SignedValInt.toInt_ofInt,
          qge2SignedPatternOne_sum hm2]
      exact ⟨∑ i ∈ J, SignedValInt.toInt (x i),
        Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
    · let x : Fin (m + m) → SignedValInt :=
        fun i => SignedValInt.ofInt
          (qge2SignedPatternTwo m i)
          (qge2SignedPatternTwo_isSigned (m := m) i)
      have hx : x ∈ qge2SignedColumnFinset (m + m) 2 := by
        simp [qge2SignedColumnFinset, x, SignedValInt.toInt_ofInt,
          qge2SignedPatternTwo_sum hm2]
      exact ⟨∑ i ∈ J, SignedValInt.toInt (x i),
        Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  rcases hvals_nonempty with ⟨z0, hz0⟩
  rcases Finset.max_of_mem hz0 with ⟨zmax, hmax⟩
  have hmax_le_withBot :
      vals.max ≤ (qge2ColumnCapacity n J.card c : WithBot Int) :=
    Finset.max_le (s := vals) (M := (qge2ColumnCapacity n J.card c : WithBot Int))
      (by
        intro z hz
        exact_mod_cast hvals_bound z hz)
  have hmax_le : zmax ≤ qge2ColumnCapacity n J.card c := by
    simpa [hmax] using hmax_le_withBot
  simpa [qge2SignedColumnSupport, vals, w, indicator_weight_sum, hmax] using hmax_le

theorem ordinaryQge2SignedFullSupportTrellisGoal_of_seedClosure
    (hClosure : OrdinaryQge2SignedSeedClosureGoal) :
    OrdinaryQge2SignedFullSupportTrellisGoal := by
  classical
  intro n r hnEven hn4 hrOdd hrlt hrpos a epsBit c
    ha heps hc heps_sum ha_eq_c hSupport
  let C : Nat := ∑ k : Fin (n - 1), c k
  have hCuts :
      ∀ J : Finset (Fin n),
        (∑ i ∈ J, ((r : Int) - (a i : Int)
            - (n : Int) * (epsBit i : Int)))
          ≤ ∑ k : Fin (n - 1), qge2ColumnCapacity n J.card (c k) := by
    intro J
    have h :=
      hSupport (fun i : Fin n => if i ∈ J then (1 : Int) else 0)
    have hleft :
        (∑ i : Fin n,
          (if i ∈ J then (1 : Int) else 0)
            * qge2OrdinaryRowTarget n r a epsBit i)
          =
        ∑ i ∈ J, ((r : Int) - (a i : Int)
            - (n : Int) * (epsBit i : Int)) := by
      simp [qge2OrdinaryRowTarget]
    have hright :
        (∑ k : Fin (n - 1),
          qge2SignedColumnSupport n (c k)
            (fun i : Fin n => if i ∈ J then (1 : Int) else 0))
          ≤
        ∑ k : Fin (n - 1), qge2ColumnCapacity n J.card (c k) := by
      apply Finset.sum_le_sum
      intro k _hk
      exact qge2SignedColumnSupport_indicator_le_capacity
        hnEven hn4 (hc k) J
    have h' :
        (∑ i ∈ J, ((r : Int) - (a i : Int)
            - (n : Int) * (epsBit i : Int)))
          ≤ ∑ k : Fin (n - 1),
              qge2SignedColumnSupport n (c k)
                (fun i : Fin n => if i ∈ J then (1 : Int) else 0) := by
      rw [← hleft]
      exact h
    exact le_trans h' hright
  rcases hClosure (n := n) (C := C) (r := r)
      hnEven hn4 hrOdd hrlt hrpos
      a epsBit c ha heps hc
      (by simpa [C] using ha_eq_c)
      heps_sum
      (by simp [C])
      hCuts with ⟨S, hSsigned, hSrow, hScol⟩
  refine ⟨fun k i => S i k, ?_, ?_, ?_⟩
  · intro k i
    exact hSsigned i k
  · intro k
    exact hScol k
  · intro i
    simpa [qge2OrdinaryRowTarget] using hSrow i

theorem ordinaryQge2SignedSeedProperCutClosureGoal_of_fullSupportTrellisGoal
    (hFull : OrdinaryQge2SignedFullSupportTrellisGoal) :
    OrdinaryQge2SignedSeedProperCutClosureGoal :=
  ordinaryQge2SignedSeedProperCutClosureGoal_of_signedTrellisHoffman
    (ordinaryQge2SignedTrellisHoffmanGoal_of_fullSupport hFull
      ordinaryQge2IndicatorToFullSupportGoal_of_internalHalfSlack)

theorem ordinaryQge2SignedFullSupportTrellisGoal_iff_seedProperCutClosureGoal :
    OrdinaryQge2SignedFullSupportTrellisGoal ↔
      OrdinaryQge2SignedSeedProperCutClosureGoal :=
  ⟨ordinaryQge2SignedSeedProperCutClosureGoal_of_fullSupportTrellisGoal,
    fun hProper =>
      ordinaryQge2SignedFullSupportTrellisGoal_of_seedClosure
        (ordinaryQge2SignedSeedClosureGoal_of_properCutClosure hProper)⟩

end PrefixCount
end RoundComposite
