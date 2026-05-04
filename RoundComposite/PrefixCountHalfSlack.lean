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

end PrefixCount
end RoundComposite
