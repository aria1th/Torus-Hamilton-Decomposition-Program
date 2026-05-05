import RoundComposite.PrefixCountHalfSlack

namespace RoundComposite
namespace PrefixCount

open scoped BigOperators

/--
An alternate `c = 2` signed pattern used only for the middle indicator cut.
The older half-slack pattern is intentionally one unit below the middle cut;
this one attains the exact indicator capacity at `|J| = n / 2`.
-/
def qge2SignedPatternTwoMiddle (m : Nat) (j : Fin (m + m)) : Int :=
  -2 + (if j.val < m then 3 else 0) +
    (if j.val < m - 2 then 1 else 0)

theorem qge2SignedPatternTwoMiddle_isSigned {m : Nat} (hm2 : 2 ≤ m)
    (j : Fin (m + m)) :
    IsSignedVal (qge2SignedPatternTwoMiddle m j) := by
  unfold qge2SignedPatternTwoMiddle
  by_cases hlt : j.val < m
  · by_cases hlt2 : j.val < m - 2
    · simp [hlt, hlt2, IsSignedVal, signedVals]
    · simp [hlt, hlt2, IsSignedVal, signedVals]
  · have hlt2 : ¬ j.val < m - 2 := by omega
    simp [hlt, hlt2, IsSignedVal, signedVals]

theorem qge2SignedPatternTwoMiddle_sum {m : Nat} (hm2 : 2 ≤ m) :
    (∑ j : Fin (m + m), qge2SignedPatternTwoMiddle m j) = -2 := by
  classical
  have hm_le : m ≤ m + m := by omega
  have hm2_le : m - 2 ≤ m + m := by omega
  have hsum_m :
      (∑ j : Fin (m + m), if j.val < m then (3 : Int) else 0)
        = 3 * (m : Int) := by
    rw [fin_sum_if_val_lt_eq_fin_sum
      (n := m + m) (q := m) hm_le (fun _ => (3 : Int))]
    simp [Finset.sum_const, Fintype.card_fin, mul_comm]
  have hsum_m2 :
      (∑ j : Fin (m + m), if j.val < m - 2 then (1 : Int) else 0)
        = ((m - 2 : Nat) : Int) := by
    rw [fin_sum_if_val_lt_eq_fin_sum
      (n := m + m) (q := m - 2) hm2_le (fun _ => (1 : Int))]
    simp [Finset.sum_const, Fintype.card_fin]
  calc
    (∑ j : Fin (m + m), qge2SignedPatternTwoMiddle m j)
        =
      (∑ _j : Fin (m + m), (-2 : Int))
        + (∑ j : Fin (m + m), if j.val < m then (3 : Int) else 0)
        + (∑ j : Fin (m + m), if j.val < m - 2 then (1 : Int) else 0) := by
          simp [qge2SignedPatternTwoMiddle, Finset.sum_add_distrib,
            add_assoc]
    _ = -2 := by
          rw [hsum_m, hsum_m2]
          simp [Finset.sum_const, Fintype.card_fin]
          omega

theorem qge2SignedPatternTwoMiddle_prefix_middle {m : Nat} (hm2 : 2 ≤ m) :
    (∑ j : Fin (m + m),
        if j.val < m then qge2SignedPatternTwoMiddle m j else 0)
      = qge2ColumnCapacity (m + m) m 2 := by
  classical
  have hm_le : m ≤ m + m := by omega
  have hm2_le : m - 2 ≤ m := by omega
  have hsmall :
      (∑ a : Fin m, if a.val < m - 2 then (1 : Int) else 0)
        = ((m - 2 : Nat) : Int) := by
    rw [fin_sum_if_val_lt_eq_fin_sum
      (n := m) (q := m - 2) hm2_le (fun _ => (1 : Int))]
    simp [Finset.sum_const, Fintype.card_fin]
  calc
    (∑ j : Fin (m + m),
        if j.val < m then qge2SignedPatternTwoMiddle m j else 0)
        =
      ∑ a : Fin m, qge2SignedPatternTwoMiddle m (Fin.castLE hm_le a) := by
        rw [fin_sum_if_val_lt_eq_fin_sum
          (n := m + m) (q := m) hm_le
          (qge2SignedPatternTwoMiddle m)]
    _ =
      ∑ a : Fin m, ((1 : Int) + if a.val < m - 2 then (1 : Int) else 0) := by
        apply Finset.sum_congr rfl
        intro a _ha
        simp [qge2SignedPatternTwoMiddle, a.isLt]
    _ = (m : Int) + ((m - 2 : Nat) : Int) := by
        rw [Finset.sum_add_distrib, hsmall]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          Int.nsmul_eq_mul, mul_one]
    _ = qge2ColumnCapacity (m + m) m 2 := by
        have hcap :
            qge2ColumnCapacity (m + m) m 2 =
              2 * (((m + m) - m : Nat) : Int) - (2 : Int) :=
          qge2ColumnCapacity_eq_right (by omega)
        rw [hcap]
        omega

theorem qge2SignedColumnSupport_one_indicator_ge_capacity
    {m : Nat} (hm2 : 2 ≤ m) (J : Finset (Fin (m + m))) :
    qge2ColumnCapacity (m + m) J.card 1
      ≤ qge2SignedColumnSupport (m + m) 1
          (fun i : Fin (m + m) => if i ∈ J then (1 : Int) else 0) := by
  classical
  let u : Fin (m + m) → Nat := fun i => if i ∈ J then 1 else 0
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
      (∑ i : Fin (m + m), (if i ∈ J then (1 : Int) else 0) * v i)
        ≤ qge2SignedColumnSupport (m + m) 1
            (fun i : Fin (m + m) => if i ∈ J then (1 : Int) else 0) :=
    qge2SignedColumnSupport_ge_of_intColumn
      (n := m + m) (c := 1)
      (fun i : Fin (m + m) => if i ∈ J then (1 : Int) else 0)
      hv hsumv
  have hUpper : qge2UpperLevel u 0 = J := by
    ext i
    by_cases hi : i ∈ J <;> simp [qge2UpperLevel, u, hi]
  have hq : J.card ≤ m + m := by
    simpa [Fintype.card_fin] using Finset.card_le_univ (s := J)
  have hcap :
      qge2ColumnCapacity (m + m) J.card 1
        ≤ qge2SignedPatternPrefixOne m J.card :=
    qge2SignedPatternPrefixOne_capacity (m := m) (q := J.card) hm2 hq
  have hprefix :
      (∑ j : Fin (m + m),
        if j.val < J.card then qge2SignedPatternOne m j else 0)
        = qge2SignedPatternPrefixOne m J.card :=
    qge2SignedPatternOne_prefix_sum (m := m) (q := J.card) hm2 hq
  have hsorted :
      (∑ i ∈ J, v i)
        =
      ∑ j : Fin (m + m),
        if j.val < J.card then qge2SignedPatternOne m j else 0 := by
    have h :=
      qge2UpperLevel_sorted_pattern_sum
        (n := m + m) u 0 (qge2SignedPatternOne m)
    simpa [hUpper, u, σ, v] using h
  have hdot :
      (∑ i : Fin (m + m), (if i ∈ J then (1 : Int) else 0) * v i)
        = ∑ i ∈ J, v i :=
    indicator_weight_sum J v
  calc
    qge2ColumnCapacity (m + m) J.card 1
        ≤ qge2SignedPatternPrefixOne m J.card := hcap
    _ = ∑ j : Fin (m + m),
          if j.val < J.card then qge2SignedPatternOne m j else 0 :=
          hprefix.symm
    _ = ∑ i ∈ J, v i := hsorted.symm
    _ = ∑ i : Fin (m + m),
          (if i ∈ J then (1 : Int) else 0) * v i := hdot.symm
    _ ≤ qge2SignedColumnSupport (m + m) 1
          (fun i : Fin (m + m) => if i ∈ J then (1 : Int) else 0) :=
          hsupport

theorem qge2SignedColumnSupport_two_indicator_ge_capacity
    {m : Nat} (hm2 : 2 ≤ m) (J : Finset (Fin (m + m))) :
    qge2ColumnCapacity (m + m) J.card 2
      ≤ qge2SignedColumnSupport (m + m) 2
          (fun i : Fin (m + m) => if i ∈ J then (1 : Int) else 0) := by
  classical
  let u : Fin (m + m) → Nat := fun i => if i ∈ J then 1 else 0
  let σ : Equiv.Perm (Fin (m + m)) :=
    Tuple.sort (fun i : Fin (m + m) => -((u i : Int)))
  by_cases hmid : J.card = m
  · let v : Fin (m + m) → Int :=
      fun i => qge2SignedPatternTwoMiddle m (σ.symm i)
    have hv : ∀ i : Fin (m + m), IsSignedVal (v i) := by
      intro i
      exact qge2SignedPatternTwoMiddle_isSigned (m := m) hm2 (σ.symm i)
    have hsumv : (∑ i : Fin (m + m), v i) = -2 := by
      calc
        (∑ i : Fin (m + m), v i)
            = ∑ j : Fin (m + m), qge2SignedPatternTwoMiddle m j := by
              simpa [v] using
                (Equiv.sum_comp σ.symm (fun j : Fin (m + m) =>
                  qge2SignedPatternTwoMiddle m j))
        _ = -2 := qge2SignedPatternTwoMiddle_sum hm2
    have hsupport :
        (∑ i : Fin (m + m), (if i ∈ J then (1 : Int) else 0) * v i)
          ≤ qge2SignedColumnSupport (m + m) 2
              (fun i : Fin (m + m) => if i ∈ J then (1 : Int) else 0) :=
      qge2SignedColumnSupport_ge_of_intColumn
        (n := m + m) (c := 2)
        (fun i : Fin (m + m) => if i ∈ J then (1 : Int) else 0)
        hv hsumv
    have hUpper : qge2UpperLevel u 0 = J := by
      ext i
      by_cases hi : i ∈ J <;> simp [qge2UpperLevel, u, hi]
    have hsorted :
        (∑ i ∈ J, v i)
          =
        ∑ j : Fin (m + m),
          if j.val < J.card then qge2SignedPatternTwoMiddle m j else 0 := by
      have h :=
        qge2UpperLevel_sorted_pattern_sum
          (n := m + m) u 0 (qge2SignedPatternTwoMiddle m)
      simpa [hUpper, u, σ, v] using h
    have hdot :
        (∑ i : Fin (m + m), (if i ∈ J then (1 : Int) else 0) * v i)
          = ∑ i ∈ J, v i :=
      indicator_weight_sum J v
    calc
      qge2ColumnCapacity (m + m) J.card 2
          =
        qge2ColumnCapacity (m + m) m 2 := by rw [hmid]
      _ = ∑ j : Fin (m + m),
            if j.val < m then qge2SignedPatternTwoMiddle m j else 0 :=
            (qge2SignedPatternTwoMiddle_prefix_middle hm2).symm
      _ = ∑ j : Fin (m + m),
            if j.val < J.card then qge2SignedPatternTwoMiddle m j else 0 := by
            rw [hmid]
      _ = ∑ i ∈ J, v i := hsorted.symm
      _ = ∑ i : Fin (m + m),
            (if i ∈ J then (1 : Int) else 0) * v i := hdot.symm
      _ ≤ qge2SignedColumnSupport (m + m) 2
            (fun i : Fin (m + m) => if i ∈ J then (1 : Int) else 0) :=
            hsupport
  · let v : Fin (m + m) → Int :=
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
        (∑ i : Fin (m + m), (if i ∈ J then (1 : Int) else 0) * v i)
          ≤ qge2SignedColumnSupport (m + m) 2
              (fun i : Fin (m + m) => if i ∈ J then (1 : Int) else 0) :=
      qge2SignedColumnSupport_ge_of_intColumn
        (n := m + m) (c := 2)
        (fun i : Fin (m + m) => if i ∈ J then (1 : Int) else 0)
        hv hsumv
    have hUpper : qge2UpperLevel u 0 = J := by
      ext i
      by_cases hi : i ∈ J <;> simp [qge2UpperLevel, u, hi]
    have hq : J.card ≤ m + m := by
      simpa [Fintype.card_fin] using Finset.card_le_univ (s := J)
    have hcap :
        qge2ColumnCapacity (m + m) J.card 2
          ≤ qge2SignedPatternPrefixTwo m J.card := by
      have h :=
        qge2SignedPatternPrefixTwo_capacity_sub_half
          (m := m) (q := J.card) hm2 hq
      simpa [hmid] using h
    have hprefix :
        (∑ j : Fin (m + m),
          if j.val < J.card then qge2SignedPatternTwo m j else 0)
          = qge2SignedPatternPrefixTwo m J.card :=
      qge2SignedPatternTwo_prefix_sum (m := m) (q := J.card) hm2 hq
    have hsorted :
        (∑ i ∈ J, v i)
          =
        ∑ j : Fin (m + m),
          if j.val < J.card then qge2SignedPatternTwo m j else 0 := by
      have h :=
        qge2UpperLevel_sorted_pattern_sum
          (n := m + m) u 0 (qge2SignedPatternTwo m)
      simpa [hUpper, u, σ, v] using h
    have hdot :
        (∑ i : Fin (m + m), (if i ∈ J then (1 : Int) else 0) * v i)
          = ∑ i ∈ J, v i :=
      indicator_weight_sum J v
    calc
      qge2ColumnCapacity (m + m) J.card 2
          ≤ qge2SignedPatternPrefixTwo m J.card := hcap
      _ = ∑ j : Fin (m + m),
            if j.val < J.card then qge2SignedPatternTwo m j else 0 :=
            hprefix.symm
      _ = ∑ i ∈ J, v i := hsorted.symm
      _ = ∑ i : Fin (m + m),
            (if i ∈ J then (1 : Int) else 0) * v i := hdot.symm
      _ ≤ qge2SignedColumnSupport (m + m) 2
            (fun i : Fin (m + m) => if i ∈ J then (1 : Int) else 0) :=
            hsupport

theorem qge2SignedColumnSupport_indicator_ge_capacity
    {n c : Nat} (hnEven : Even n) (hn4 : 4 ≤ n)
    (hc : c = 1 ∨ c = 2) (J : Finset (Fin n)) :
    qge2ColumnCapacity n J.card c
      ≤ qge2SignedColumnSupport n c
          (fun i : Fin n => if i ∈ J then (1 : Int) else 0) := by
  classical
  rcases hnEven with ⟨m, rfl⟩
  have hm2 : 2 ≤ m := by omega
  rcases hc with rfl | rfl
  · exact qge2SignedColumnSupport_one_indicator_ge_capacity hm2 J
  · exact qge2SignedColumnSupport_two_indicator_ge_capacity hm2 J

theorem qge2SignedColumnSupport_indicator_eq_capacity
    {n c : Nat} (hnEven : Even n) (hn4 : 4 ≤ n)
    (hc : c = 1 ∨ c = 2) (J : Finset (Fin n)) :
    qge2SignedColumnSupport n c
        (fun i : Fin n => if i ∈ J then (1 : Int) else 0)
      = qge2ColumnCapacity n J.card c :=
  le_antisymm
    (qge2SignedColumnSupport_indicator_le_capacity hnEven hn4 hc J)
    (qge2SignedColumnSupport_indicator_ge_capacity hnEven hn4 hc J)

theorem sum_qge2SignedColumnSupport_indicator_eq_capacity
    {n : Nat} (hnEven : Even n) (hn4 : 4 ≤ n)
    {c : Fin (n - 1) → Nat}
    (hc : ∀ k : Fin (n - 1), c k = 1 ∨ c k = 2)
    (J : Finset (Fin n)) :
    (∑ k : Fin (n - 1),
        qge2SignedColumnSupport n (c k)
          (fun i : Fin n => if i ∈ J then (1 : Int) else 0))
      =
    ∑ k : Fin (n - 1), qge2ColumnCapacity n J.card (c k) := by
  classical
  apply Finset.sum_congr rfl
  intro k _hk
  exact qge2SignedColumnSupport_indicator_eq_capacity
    hnEven hn4 (hc k) J

theorem qge2IndicatorCuts_of_fullSupportCuts
    {n r : Nat} (hnEven : Even n) (hn4 : 4 ≤ n)
    (a : Fin n → Nat) (epsBit : Fin n → Nat)
    (c : Fin (n - 1) → Nat)
    (hc : ∀ k : Fin (n - 1), c k = 1 ∨ c k = 2)
    (hSupport : ∀ w : Fin n → Int,
      (∑ i : Fin n, w i * qge2OrdinaryRowTarget n r a epsBit i)
        ≤ ∑ k : Fin (n - 1), qge2SignedColumnSupport n (c k) w) :
    ∀ J : Finset (Fin n),
      (∑ i ∈ J, qge2OrdinaryRowTarget n r a epsBit i)
        ≤ ∑ k : Fin (n - 1), qge2ColumnCapacity n J.card (c k) := by
  classical
  intro J
  have h := hSupport (fun i : Fin n => if i ∈ J then (1 : Int) else 0)
  rw [indicator_weight_sum J (qge2OrdinaryRowTarget n r a epsBit)] at h
  rw [sum_qge2SignedColumnSupport_indicator_eq_capacity
    hnEven hn4 hc J] at h
  exact h

theorem qge2FullSupportCuts_iff_indicatorCuts
    {n r : Nat} (hnEven : Even n) (hn4 : 4 ≤ n)
    (hrOdd : Odd r) (hrlt : r < n) (hrpos : 0 < r)
    (a : Fin n → Nat) (epsBit : Fin n → Nat)
    (c : Fin (n - 1) → Nat)
    (ha : ∀ i : Fin n, a i = 1 ∨ a i = 2)
    (heps : ∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1)
    (hc : ∀ k : Fin (n - 1), c k = 1 ∨ c k = 2)
    (heps_sum : (∑ i : Fin n, epsBit i) = r)
    (ha_eq_c : (∑ i : Fin n, a i) = (∑ k : Fin (n - 1), c k)) :
    (∀ w : Fin n → Int,
      (∑ i : Fin n, w i * qge2OrdinaryRowTarget n r a epsBit i)
        ≤ ∑ k : Fin (n - 1), qge2SignedColumnSupport n (c k) w) ↔
    (∀ J : Finset (Fin n),
      (∑ i ∈ J, qge2OrdinaryRowTarget n r a epsBit i)
        ≤ ∑ k : Fin (n - 1), qge2ColumnCapacity n J.card (c k)) := by
  constructor
  · intro hSupport
    exact qge2IndicatorCuts_of_fullSupportCuts
      hnEven hn4 a epsBit c hc hSupport
  · intro hCuts w
    exact ordinaryQge2IndicatorToFullSupportGoal_of_internalHalfSlack
      hnEven hn4 hrOdd hrlt hrpos a epsBit c
      ha heps hc heps_sum ha_eq_c hCuts w

def qge2LayeredSignedEntry (A B : Nat) : Int :=
  -2 + (A : Int) + 3 * (B : Int)

theorem qge2LayeredSignedEntry_isSigned {A B : Nat}
    (hA : A = 0 ∨ A = 1) (hB : B = 0 ∨ B = 1) :
    IsSignedVal (qge2LayeredSignedEntry A B) := by
  rcases hA with rfl | rfl <;>
    rcases hB with rfl | rfl <;>
      simp [qge2LayeredSignedEntry, IsSignedVal, signedVals]

theorem exists_nat_add_three_mul_eq_of_le_four_mul {N D : Nat}
    (hN : 2 ≤ N) (hD : D ≤ 4 * N) :
    ∃ A B : Nat, A ≤ N ∧ B ≤ N ∧ A + 3 * B = D := by
  by_cases hD3 : D ≤ 3 * N
  · refine ⟨D % 3, D / 3, ?_, ?_, ?_⟩
    · have hmod : D % 3 < 3 := Nat.mod_lt D (by decide : 0 < 3)
      omega
    · exact Nat.div_le_of_le_mul hD3
    · exact Nat.mod_add_div D 3
  · refine ⟨D - 3 * N, N, ?_, le_rfl, ?_⟩
    · omega
    · omega

def qge2LayeredRowTargetNat (n r : Nat)
    (a epsBit : Fin n → Nat) (i : Fin n) : Nat :=
  r + 2 * (n - 1) - a i - n * epsBit i

theorem qge2LayeredRowTargetNat_cast {n r : Nat}
    (hn4 : 4 ≤ n) {a epsBit : Fin n → Nat} {i : Fin n}
    (ha : a i = 1 ∨ a i = 2)
    (heps : epsBit i = 0 ∨ epsBit i = 1) :
    ((qge2LayeredRowTargetNat n r a epsBit i : Nat) : Int) =
      qge2OrdinaryRowTarget n r a epsBit i +
        2 * ((n - 1 : Nat) : Int) := by
  rcases ha with ha | ha <;> rcases heps with heps | heps <;>
    simp [qge2LayeredRowTargetNat, qge2OrdinaryRowTarget, ha, heps] <;> omega

theorem qge2LayeredRowTargetNat_le_four_cols {n r : Nat}
    (hn4 : 4 ≤ n) (hrlt : r < n)
    {a epsBit : Fin n → Nat} (i : Fin n)
    (ha : a i = 1 ∨ a i = 2)
    (heps : epsBit i = 0 ∨ epsBit i = 1) :
    qge2LayeredRowTargetNat n r a epsBit i ≤ 4 * (n - 1) := by
  rcases ha with ha | ha <;> rcases heps with heps | heps <;>
    simp [qge2LayeredRowTargetNat, ha, heps] <;> omega

theorem exists_qge2LayeredRowTargetNat_split {n r : Nat}
    (hn4 : 4 ≤ n) (hrlt : r < n)
    {a epsBit : Fin n → Nat} (i : Fin n)
    (ha : a i = 1 ∨ a i = 2)
    (heps : epsBit i = 0 ∨ epsBit i = 1) :
    ∃ A B : Nat, A ≤ n - 1 ∧ B ≤ n - 1 ∧
      A + 3 * B = qge2LayeredRowTargetNat n r a epsBit i := by
  exact exists_nat_add_three_mul_eq_of_le_four_mul (by omega)
    (qge2LayeredRowTargetNat_le_four_cols hn4 hrlt i ha heps)

theorem exists_qge2LayeredRowTarget_split_int {n r : Nat}
    (hn4 : 4 ≤ n) (hrlt : r < n)
    {a epsBit : Fin n → Nat} (i : Fin n)
    (ha : a i = 1 ∨ a i = 2)
    (heps : epsBit i = 0 ∨ epsBit i = 1) :
    ∃ A B : Nat, A ≤ n - 1 ∧ B ≤ n - 1 ∧
      (A : Int) + 3 * (B : Int) =
        qge2OrdinaryRowTarget n r a epsBit i +
          2 * ((n - 1 : Nat) : Int) := by
  rcases exists_qge2LayeredRowTargetNat_split hn4 hrlt i ha heps with
    ⟨A, B, hA, hB, hsum⟩
  refine ⟨A, B, hA, hB, ?_⟩
  have hsumInt :
      (A : Int) + 3 * (B : Int) =
        (qge2LayeredRowTargetNat n r a epsBit i : Int) := by
    exact_mod_cast hsum
  rw [hsumInt, qge2LayeredRowTargetNat_cast hn4 ha heps]

def qge2LayeredColumnTargetNat (n c : Nat) : Nat :=
  2 * n - c

theorem qge2LayeredColumnTargetNat_cast {n c : Nat}
    (hn4 : 4 ≤ n) (hc : c = 1 ∨ c = 2) :
    ((qge2LayeredColumnTargetNat n c : Nat) : Int) =
      2 * (n : Int) - (c : Int) := by
  rcases hc with rfl | rfl <;>
    simp [qge2LayeredColumnTargetNat] <;> omega

theorem qge2LayeredColumnTargetNat_le_four_rows {n c : Nat}
    (hc : c = 1 ∨ c = 2) :
    qge2LayeredColumnTargetNat n c ≤ 4 * n := by
  rcases hc with rfl | rfl <;>
    simp [qge2LayeredColumnTargetNat] <;> omega

theorem exists_qge2LayeredColumnTargetNat_split {n c : Nat}
    (hn4 : 4 ≤ n) (hc : c = 1 ∨ c = 2) :
    ∃ A B : Nat, A ≤ n ∧ B ≤ n ∧
      A + 3 * B = qge2LayeredColumnTargetNat n c := by
  exact exists_nat_add_three_mul_eq_of_le_four_mul (by omega)
    (qge2LayeredColumnTargetNat_le_four_rows hc)

theorem exists_qge2LayeredColumnTarget_split_int {n c : Nat}
    (hn4 : 4 ≤ n) (hc : c = 1 ∨ c = 2) :
    ∃ A B : Nat, A ≤ n ∧ B ≤ n ∧
      (A : Int) + 3 * (B : Int) = 2 * (n : Int) - (c : Int) := by
  rcases exists_qge2LayeredColumnTargetNat_split hn4 hc with
    ⟨A, B, hA, hB, hsum⟩
  refine ⟨A, B, hA, hB, ?_⟩
  have hsumInt :
      (A : Int) + 3 * (B : Int) =
        (qge2LayeredColumnTargetNat n c : Int) := by
    exact_mod_cast hsum
  rw [hsumInt, qge2LayeredColumnTargetNat_cast hn4 hc]

theorem qge2LayeredColumnTarget_uniformB_A_le {m c : Nat}
    (hm2 : 2 ≤ m) (hc : c = 1 ∨ c = 2) :
    m - c ≤ m + m := by
  rcases hc with rfl | rfl <;> omega

theorem qge2LayeredColumnTarget_uniformB_split_int {m c : Nat}
    (hm2 : 2 ≤ m) (hc : c = 1 ∨ c = 2) :
    ((m - c : Nat) : Int) + 3 * (m : Int) =
      2 * ((m + m : Nat) : Int) - (c : Int) := by
  rcases hc with rfl | rfl <;> omega

def qge2LayeredBRowLo (n r : Nat)
    (a epsBit : Fin n → Nat) (i : Fin n) : Nat :=
  let D := qge2LayeredRowTargetNat n r a epsBit i
  let cols := n - 1
  if D ≤ cols then 0 else (D - cols + 2) / 3

def qge2LayeredBRowHi (n r : Nat)
    (a epsBit : Fin n → Nat) (i : Fin n) : Nat :=
  qge2LayeredRowTargetNat n r a epsBit i / 3

theorem qge2LayeredBRowLo_le_hi {n r : Nat}
    (hn4 : 4 ≤ n) (a epsBit : Fin n → Nat) (i : Fin n) :
    qge2LayeredBRowLo n r a epsBit i ≤
      qge2LayeredBRowHi n r a epsBit i := by
  unfold qge2LayeredBRowLo qge2LayeredBRowHi
  by_cases hD :
      qge2LayeredRowTargetNat n r a epsBit i ≤ n - 1
  · rw [if_pos hD]
    exact Nat.zero_le _
  · rw [if_neg hD]
    apply Nat.div_le_div_right
    omega

theorem qge2LayeredBRowHi_spec {n r B : Nat}
    {a epsBit : Fin n → Nat} {i : Fin n}
    (hB : B ≤ qge2LayeredBRowHi n r a epsBit i) :
    3 * B ≤ qge2LayeredRowTargetNat n r a epsBit i := by
  unfold qge2LayeredBRowHi at hB
  simpa [mul_comm] using
    (Nat.le_div_iff_mul_le (by decide : 0 < 3)).1 hB

theorem qge2LayeredBRowLo_spec {n r B : Nat}
    {a epsBit : Fin n → Nat} {i : Fin n}
    (hB : qge2LayeredBRowLo n r a epsBit i ≤ B) :
    qge2LayeredRowTargetNat n r a epsBit i ≤ 3 * B + (n - 1) := by
  unfold qge2LayeredBRowLo at hB
  by_cases hD :
      qge2LayeredRowTargetNat n r a epsBit i ≤ n - 1
  · rw [if_pos hD] at hB
    omega
  · rw [if_neg hD] at hB
    have hlt :
        qge2LayeredRowTargetNat n r a epsBit i - (n - 1) + 2 <
          (B + 1) * 3 := by
      exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).1
        (Nat.lt_succ_of_le hB)
    omega

theorem exists_qge2LayeredRowTargetNat_split_of_B_between {n r B : Nat}
    {a epsBit : Fin n → Nat} {i : Fin n}
    (hlo : qge2LayeredBRowLo n r a epsBit i ≤ B)
    (hhi : B ≤ qge2LayeredBRowHi n r a epsBit i) :
    ∃ A : Nat, A ≤ n - 1 ∧
      A + 3 * B = qge2LayeredRowTargetNat n r a epsBit i := by
  let D := qge2LayeredRowTargetNat n r a epsBit i
  have hleD : 3 * B ≤ D := by
    dsimp [D]
    exact qge2LayeredBRowHi_spec hhi
  have hleCols : D ≤ 3 * B + (n - 1) := by
    dsimp [D]
    exact qge2LayeredBRowLo_spec hlo
  refine ⟨D - 3 * B, ?_, ?_⟩ <;> omega

theorem exists_qge2LayeredRowTarget_split_int_of_B_between {n r B : Nat}
    (hn4 : 4 ≤ n)
    {a epsBit : Fin n → Nat} {i : Fin n}
    (ha : a i = 1 ∨ a i = 2)
    (heps : epsBit i = 0 ∨ epsBit i = 1)
    (hlo : qge2LayeredBRowLo n r a epsBit i ≤ B)
    (hhi : B ≤ qge2LayeredBRowHi n r a epsBit i) :
    ∃ A : Nat, A ≤ n - 1 ∧
      (A : Int) + 3 * (B : Int) =
        qge2OrdinaryRowTarget n r a epsBit i +
          2 * ((n - 1 : Nat) : Int) := by
  rcases exists_qge2LayeredRowTargetNat_split_of_B_between
      (n := n) (r := r) (B := B) (a := a) (epsBit := epsBit) (i := i)
      hlo hhi with ⟨A, hA, hsum⟩
  refine ⟨A, hA, ?_⟩
  have hsumInt :
      (A : Int) + 3 * (B : Int) =
        (qge2LayeredRowTargetNat n r a epsBit i : Int) := by
    exact_mod_cast hsum
  rw [hsumInt, qge2LayeredRowTargetNat_cast hn4 ha heps]

theorem qge2LayeredBRowLo_triple_le {n r : Nat}
    {a epsBit : Fin n → Nat} {i : Fin n}
    (hn4 : 4 ≤ n) (hrpos : 0 < r)
    (ha : a i = 1 ∨ a i = 2)
    (heps : epsBit i = 0 ∨ epsBit i = 1) :
    (3 * qge2LayeredBRowLo n r a epsBit i : Int) ≤
      (r : Int) + (n : Int) - (n : Int) * (epsBit i : Int)
        - (a i : Int) + 1 := by
  unfold qge2LayeredBRowLo qge2LayeredRowTargetNat
  by_cases hD : r + 2 * (n - 1) - a i - n * epsBit i ≤ n - 1
  · rw [if_pos hD]
    rcases ha with ha | ha <;> rcases heps with heps | heps <;>
      simp [ha, heps] at hD ⊢ <;> omega
  · rw [if_neg hD]
    have hmul :
        3 * ((r + 2 * (n - 1) - a i - n * epsBit i - (n - 1) + 2) / 3)
          ≤ r + 2 * (n - 1) - a i - n * epsBit i - (n - 1) + 2 := by
      simpa [mul_comm] using
        Nat.div_mul_le_self
          (r + 2 * (n - 1) - a i - n * epsBit i - (n - 1) + 2) 3
    have hmulInt :
        ((3 * ((r + 2 * (n - 1) - a i - n * epsBit i - (n - 1) + 2) / 3) : Nat) :
            Int) ≤
          (r + 2 * (n - 1) - a i - n * epsBit i - (n - 1) + 2 : Nat) := by
      exact_mod_cast hmul
    have hXle :
        ((r + 2 * (n - 1) - a i - n * epsBit i - (n - 1) + 2 : Nat) :
            Int) ≤
          (r : Int) + (n : Int) - (n : Int) * (epsBit i : Int)
            - (a i : Int) + 1 := by
      rcases ha with ha | ha <;> rcases heps with heps | heps <;>
        simp [ha, heps] at hD ⊢ <;> omega
    exact hmulInt.trans hXle

theorem qge2LayeredBRowHi_triple_ge {n r : Nat}
    (a epsBit : Fin n → Nat) (i : Fin n) :
    ((qge2LayeredRowTargetNat n r a epsBit i : Nat) : Int) - 2 ≤
      3 * (qge2LayeredBRowHi n r a epsBit i : Int) := by
  unfold qge2LayeredBRowHi
  let D := qge2LayeredRowTargetNat n r a epsBit i
  have hlt : D < 3 * (D / 3 + 1) := by
    simpa [mul_comm] using Nat.lt_mul_div_succ D (by decide : 0 < 3)
  omega

theorem qge2LayeredBRowHi_le_cols {n r : Nat}
    (hn4 : 4 ≤ n) (hrlt : r < n)
    {a epsBit : Fin n → Nat} (i : Fin n)
    (ha : a i = 1 ∨ a i = 2)
    (heps : epsBit i = 0 ∨ epsBit i = 1) :
    qge2LayeredBRowHi n r a epsBit i ≤ n - 1 := by
  unfold qge2LayeredBRowHi qge2LayeredRowTargetNat
  rcases ha with ha | ha <;> rcases heps with heps | heps <;>
    simp [ha, heps] <;>
      exact Nat.div_le_of_le_mul (by omega)

theorem uniformColumnDegreePartialBlockResidueSum
    (cols h len : Nat) (hlen : len ≤ cols) (k : Fin cols) :
    (∑ n ∈ Finset.Ico (h * cols) (h * cols + len),
      if n % cols = k.val then (1 : Nat) else 0) =
      if k.val < len then 1 else 0 := by
  classical
  by_cases hklt : k.val < len
  · have hfilter :
      (Finset.Ico (h * cols) (h * cols + len)).filter
        (fun n => n % cols = k.val) = {h * cols + k.val} := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
      constructor
      · intro hn
        rcases hn with ⟨⟨hle, hlt⟩, hmod⟩
        have htlt : n - h * cols < len := by omega
        have htltcols : n - h * cols < cols := by omega
        have hn' : n = h * cols + (n - h * cols) := by omega
        have hmodt : n % cols = n - h * cols := by
          calc
            n % cols = (h * cols + (n - h * cols)) % cols := by
              conv_lhs => rw [hn']
            _ = (n - h * cols) % cols := by
              rw [Nat.mul_add_mod_self_right]
            _ = n - h * cols := Nat.mod_eq_of_lt htltcols
        omega
      · intro hn
        subst n
        constructor
        · constructor <;> omega
        · rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt k.is_lt]
    rw [← Finset.card_filter, hfilter]
    simp [hklt]
  · have hfilter :
      (Finset.Ico (h * cols) (h * cols + len)).filter
        (fun n => n % cols = k.val) = ∅ := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.notMem_empty]
      constructor
      · intro hn
        rcases hn with ⟨⟨hle, hlt⟩, hmod⟩
        have htlt : n - h * cols < len := by omega
        have htltcols : n - h * cols < cols := by omega
        have hn' : n = h * cols + (n - h * cols) := by omega
        have hmodt : n % cols = n - h * cols := by
          calc
            n % cols = (h * cols + (n - h * cols)) % cols := by
              conv_lhs => rw [hn']
            _ = (n - h * cols) % cols := by
              rw [Nat.mul_add_mod_self_right]
            _ = n - h * cols := Nat.mod_eq_of_lt htltcols
        omega
      · intro h
        exact False.elim h
    rw [← Finset.card_filter, hfilter]
    simp [hklt]

theorem uniformColumnDegreeRangeResidueSum_mul_sub
    (cols h drop : Nat) (hcols : 0 < cols) (hh : 0 < h)
    (hdrop : drop ≤ cols) (k : Fin cols) :
    (∑ n ∈ Finset.range (h * cols - drop),
      if n % cols = k.val then (1 : Nat) else 0) =
      h - if cols - drop ≤ k.val then 1 else 0 := by
  classical
  let h' := h - 1
  let len := cols - drop
  have hhdef : h = h' + 1 := by omega
  have hmul : h * cols = h' * cols + cols := by
    have hsucc : h = h' + 1 := hhdef
    calc
      h * cols = (h' + 1) * cols := by rw [hsucc]
      _ = h' * cols + cols := by ring
  have htop : h * cols - drop = h' * cols + len := by
    rw [hmul]
    dsimp [len]
    omega
  let f : Nat → Nat := fun n => if n % cols = k.val then 1 else 0
  have hle : h' * cols ≤ h' * cols + len := by omega
  have hsplit := Finset.sum_range_add_sum_Ico (f := f) hle
  have hblock :=
    uniformColumnDegreePartialBlockResidueSum cols h' len
      (by dsimp [len]; omega) k
  have hbase := uniformColumnDegreeRangeResidueSum_mul cols h' hcols k
  rw [htop, ← hsplit, hbase]
  rw [hblock]
  by_cases hk : cols - drop ≤ k.val
  · have hnot : ¬ k.val < len := by dsimp [len]; omega
    simp [hnot, hk]
    omega
  · have hlt : k.val < len := by dsimp [len]; omega
    simp [hlt, hk]
    omega

theorem uniformColumnDegreeMatrix_col_sum_of_total_sub
    {rows cols h drop : Nat} (rowDegree : Fin rows → Nat)
    (hcols : 0 < cols) (hh : 0 < h)
    (hdrop : drop ≤ cols)
    (hrowLe : ∀ i : Fin rows, rowDegree i ≤ cols)
    (htotal : (∑ i : Fin rows, rowDegree i) = h * cols - drop)
    (k : Fin cols) :
    (∑ i : Fin rows, uniformColumnDegreeMatrix hcols rowDegree i k) =
      h - if cols - drop ≤ k.val then 1 else 0 := by
  change (∑ i : Fin rows,
      if k ∈ uniformColumnDegreeCellSet hcols rowDegree i then 1 else 0) =
    h - if cols - drop ≤ k.val then 1 else 0
  rw [uniformColumnDegreeIntervalPartitionGoal rowDegree hcols hrowLe k,
    htotal]
  exact uniformColumnDegreeRangeResidueSum_mul_sub cols h drop
    hcols hh hdrop k

theorem exists_almostUniformColumnDegreeMatrix
    {rows cols h drop : Nat} (rowDegree : Fin rows → Nat)
    (hcols : 0 < cols) (hh : 0 < h)
    (hdrop : drop ≤ cols)
    (hrowLe : ∀ i : Fin rows, rowDegree i ≤ cols)
    (htotal : (∑ i : Fin rows, rowDegree i) = h * cols - drop) :
    ∃ G : Fin rows → Fin cols → Nat,
      (∀ i k, G i k = 0 ∨ G i k = 1) ∧
      (∀ i : Fin rows, (∑ k : Fin cols, G i k) = rowDegree i) ∧
      (∀ k : Fin cols,
        (∑ i : Fin rows, G i k) =
          h - if cols - drop ≤ k.val then 1 else 0) := by
  classical
  refine ⟨uniformColumnDegreeMatrix hcols rowDegree, ?_, ?_, ?_⟩
  · intro i k
    unfold uniformColumnDegreeMatrix
    by_cases hk : k ∈ uniformColumnDegreeCellSet hcols rowDegree i
    · simp [hk]
    · simp [hk]
  · intro i
    exact uniformColumnDegreeMatrix_row_sum hcols rowDegree hrowLe i
  · intro k
    exact uniformColumnDegreeMatrix_col_sum_of_total_sub
      rowDegree hcols hh hdrop hrowLe htotal k

theorem exists_nat_between_with_sum {rows target : Nat}
    (lo hi : Fin rows → Nat)
    (hle : ∀ i : Fin rows, lo i ≤ hi i)
    (hlo : (∑ i : Fin rows, lo i) ≤ target)
    (hhi : target ≤ ∑ i : Fin rows, hi i) :
    ∃ d : Fin rows → Nat,
      (∀ i : Fin rows, lo i ≤ d i ∧ d i ≤ hi i) ∧
      (∑ i : Fin rows, d i) = target := by
  induction rows generalizing target with
  | zero =>
      refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · simp at hlo hhi ⊢
        omega
  | succ n ih =>
      let loTail : Fin n → Nat := fun i => lo i.succ
      let hiTail : Fin n → Nat := fun i => hi i.succ
      let LT := ∑ i : Fin n, loTail i
      let HT := ∑ i : Fin n, hiTail i
      let d0 := max (lo 0) (target - HT)
      have hleTail : ∀ i : Fin n, loTail i ≤ hiTail i := by
        intro i
        exact hle i.succ
      have hsumLo : (∑ i : Fin (n + 1), lo i) = lo 0 + LT := by
        rw [Fin.sum_univ_succ]
      have hsumHi : (∑ i : Fin (n + 1), hi i) = hi 0 + HT := by
        rw [Fin.sum_univ_succ]
      have hLTleHT : LT ≤ HT := by
        dsimp [LT, HT]
        exact Finset.sum_le_sum (by intro i _; exact hleTail i)
      have hd0lo : lo 0 ≤ d0 := by
        dsimp [d0]
        exact le_max_left _ _
      have hd0hi : d0 ≤ hi 0 := by
        dsimp [d0]
        apply max_le
        · exact hle 0
        · omega
      have htailLo : LT ≤ target - d0 := by
        dsimp [d0]
        omega
      have htailHi : target - d0 ≤ HT := by
        dsimp [d0]
        omega
      rcases ih loTail hiTail hleTail htailLo htailHi with
        ⟨dTail, hdTail, hsumTail⟩
      refine ⟨Fin.cons d0 dTail, ?_, ?_⟩
      · intro i
        cases i using Fin.cases with
        | zero =>
            simp [hd0lo, hd0hi]
        | succ i =>
            simpa using hdTail i
      · rw [Fin.sum_univ_succ]
        simp [hsumTail]
        omega

theorem two_mul_le_sum_min_of_six_rows_sum {t : Nat}
    (htpos : 1 ≤ t) (htle : t ≤ 5)
    (A : Fin (3 + 3) → Nat)
    (hAle : ∀ i, A i ≤ 5)
    (hAsum : (∑ i : Fin (3 + 3), A i) = 10 + 2 * t) :
    2 * t ≤ ∑ i : Fin (3 + 3), min t (A i) := by
  interval_cases t
  · have hper : ∀ i : Fin (3 + 3), A i ≤ 5 * min 1 (A i) := by
      intro i
      have hAi := hAle i
      interval_cases A i <;> simp
    have hsumLe :
        (∑ i : Fin (3 + 3), A i) ≤
          5 * ∑ i : Fin (3 + 3), min 1 (A i) := by
      calc
        (∑ i : Fin (3 + 3), A i)
            ≤ ∑ i : Fin (3 + 3), 5 * min 1 (A i) := by
              apply Finset.sum_le_sum
              intro i _
              exact hper i
        _ = 5 * ∑ i : Fin (3 + 3), min 1 (A i) := by
              rw [Finset.mul_sum]
    omega
  · have hper : ∀ i : Fin (3 + 3), A i ≤ 3 * min 2 (A i) := by
      intro i
      have hAi := hAle i
      interval_cases A i <;> simp
    have hsumLe :
        (∑ i : Fin (3 + 3), A i) ≤
          3 * ∑ i : Fin (3 + 3), min 2 (A i) := by
      calc
        (∑ i : Fin (3 + 3), A i)
            ≤ ∑ i : Fin (3 + 3), 3 * min 2 (A i) := by
              apply Finset.sum_le_sum
              intro i _
              exact hper i
        _ = 3 * ∑ i : Fin (3 + 3), min 2 (A i) := by
              rw [Finset.mul_sum]
    omega
  · have hper : ∀ i : Fin (3 + 3), A i ≤ 2 * min 3 (A i) := by
      intro i
      have hAi := hAle i
      interval_cases A i <;> simp
    have hsumLe :
        (∑ i : Fin (3 + 3), A i) ≤
          2 * ∑ i : Fin (3 + 3), min 3 (A i) := by
      calc
        (∑ i : Fin (3 + 3), A i)
            ≤ ∑ i : Fin (3 + 3), 2 * min 3 (A i) := by
              apply Finset.sum_le_sum
              intro i _
              exact hper i
        _ = 2 * ∑ i : Fin (3 + 3), min 3 (A i) := by
              rw [Finset.mul_sum]
    omega
  · have hper : ∀ i : Fin (3 + 3), A i ≤ 2 * min 4 (A i) := by
      intro i
      have hAi := hAle i
      interval_cases A i <;> simp
    have hsumLe :
        (∑ i : Fin (3 + 3), A i) ≤
          2 * ∑ i : Fin (3 + 3), min 4 (A i) := by
      calc
        (∑ i : Fin (3 + 3), A i)
            ≤ ∑ i : Fin (3 + 3), 2 * min 4 (A i) := by
              apply Finset.sum_le_sum
              intro i _
              exact hper i
        _ = 2 * ∑ i : Fin (3 + 3), min 4 (A i) := by
              rw [Finset.mul_sum]
    omega
  · have hmin : (fun i : Fin (3 + 3) => min 5 (A i)) = A := by
      funext i
      exact Nat.min_eq_right (hAle i)
    rw [hmin, hAsum]
    omega

theorem exists_c2LowExtraRowSplit_of_six_rows {t : Nat}
    (htpos : 1 ≤ t) (htle : t ≤ 5)
    (A : Fin (3 + 3) → Nat)
    (hAle : ∀ i, A i ≤ 5)
    (hAsum : (∑ i : Fin (3 + 3), A i) = 10 + 2 * t) :
    ∃ E : Fin (3 + 3) → Nat,
      (∀ i, E i ≤ A i ∧ E i ≤ t) ∧
      (∑ i : Fin (3 + 3), E i) = 2 * t := by
  let lo : Fin (3 + 3) → Nat := fun _ => 0
  let hi : Fin (3 + 3) → Nat := fun i => min t (A i)
  have hle : ∀ i, lo i ≤ hi i := by
    intro i
    exact Nat.zero_le _
  have hlo : (∑ i : Fin (3 + 3), lo i) ≤ 2 * t := by
    simp [lo]
  have hhi : 2 * t ≤ ∑ i : Fin (3 + 3), hi i := by
    simpa [hi] using
      two_mul_le_sum_min_of_six_rows_sum htpos htle A hAle hAsum
  rcases exists_nat_between_with_sum lo hi hle hlo hhi with
    ⟨E, hE, hsum⟩
  refine ⟨E, ?_, hsum⟩
  intro i
  have hEi := (hE i).2
  exact ⟨hEi.trans (Nat.min_le_right t (A i)),
    hEi.trans (Nat.min_le_left t (A i))⟩

noncomputable def finTailEquiv {cols t : Nat} (ht : t ≤ cols) :
    {j : Fin cols // cols - t ≤ j.val} ≃ Fin t where
  toFun j := ⟨j.1.val - (cols - t), by omega⟩
  invFun u := ⟨⟨cols - t + u.val, by omega⟩, by
    change cols - t ≤ cols - t + u.val
    omega⟩
  left_inv := by
    intro j
    apply Subtype.ext
    apply Fin.ext
    simp
    omega
  right_inv := by
    intro u
    apply Fin.ext
    simp

noncomputable def finHeadEquiv {cols t : Nat} (ht : t ≤ cols) :
    {j : Fin cols // j.val < cols - t} ≃ Fin (cols - t) where
  toFun j := ⟨j.1.val, j.2⟩
  invFun u := ⟨⟨u.val, by omega⟩, by exact u.2⟩
  left_inv := by
    intro j
    exact Subtype.ext rfl
  right_inv := by
    intro u
    exact Fin.ext rfl

theorem sum_dite_subtype_eq {α M : Type*} [Fintype α] [AddCommMonoid M]
    (p : α → Prop) [DecidablePred p] (f : {x // p x} → M) :
    (∑ x : α, if h : p x then f ⟨x, h⟩ else 0) =
      ∑ y : {x // p x}, f y := by
  classical
  let g : α → M := fun x => if h : p x then f ⟨x, h⟩ else 0
  have hfilter :
      (∑ x : α, g x) =
        ∑ x ∈ (Finset.univ : Finset α).filter p, g x := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : p x <;> simp [g, hx]
  rw [show (∑ x : α, if h : p x then f ⟨x, h⟩ else 0) =
      ∑ x : α, g x by rfl]
  rw [hfilter]
  rw [← Finset.sum_subtype_eq_sum_filter
    (s := (Finset.univ : Finset α)) (f := g) (p := p)]
  simp only [Finset.subtype_univ]
  apply Finset.sum_congr rfl
  intro x _
  simp [g, x.property]

theorem finTailEquiv_sum_embed {cols t : Nat} (ht : t ≤ cols)
    {M : Type*} [AddCommMonoid M] (f : Fin t → M) :
    (∑ k : Fin cols,
        if h : cols - t ≤ k.val then f (finTailEquiv ht ⟨k, h⟩) else 0)
      = ∑ u : Fin t, f u := by
  classical
  rw [sum_dite_subtype_eq
    (p := fun k : Fin cols => cols - t ≤ k.val)
    (f := fun k : {k : Fin cols // cols - t ≤ k.val} =>
      f (finTailEquiv ht k))]
  exact Fintype.sum_equiv (finTailEquiv ht) _ _ (by intro x; rfl)

theorem finTailEquiv_sum_embed_perm {cols t : Nat} (ht : t ≤ cols)
    (e : Equiv.Perm (Fin cols)) {M : Type*} [AddCommMonoid M]
    (f : Fin t → M) :
    (∑ k : Fin cols,
        if h : cols - t ≤ (e.symm k).val then
          f (finTailEquiv ht ⟨e.symm k, h⟩) else 0)
      = ∑ u : Fin t, f u := by
  classical
  let g : Fin cols → M := fun j =>
    if h : cols - t ≤ j.val then f (finTailEquiv ht ⟨j, h⟩) else 0
  calc
    (∑ k : Fin cols,
        if h : cols - t ≤ (e.symm k).val then
          f (finTailEquiv ht ⟨e.symm k, h⟩) else 0)
        = ∑ k : Fin cols, g (e.symm k) := rfl
    _ = ∑ j : Fin cols, g j := by
          simpa using (Equiv.sum_comp e.symm g)
    _ = ∑ u : Fin t, f u := by
          simpa [g] using finTailEquiv_sum_embed ht f

theorem finHeadEquiv_sum_embed {cols t : Nat} (ht : t ≤ cols)
    {M : Type*} [AddCommMonoid M] (f : Fin (cols - t) → M) :
    (∑ k : Fin cols,
        if h : k.val < cols - t then f (finHeadEquiv ht ⟨k, h⟩) else 0)
      = ∑ u : Fin (cols - t), f u := by
  classical
  rw [sum_dite_subtype_eq
    (p := fun k : Fin cols => k.val < cols - t)
    (f := fun k : {k : Fin cols // k.val < cols - t} =>
      f (finHeadEquiv ht k))]
  exact Fintype.sum_equiv (finHeadEquiv ht) _ _ (by intro x; rfl)

theorem finHeadEquiv_sum_embed_perm {cols t : Nat} (ht : t ≤ cols)
    (e : Equiv.Perm (Fin cols)) {M : Type*} [AddCommMonoid M]
    (f : Fin (cols - t) → M) :
    (∑ k : Fin cols,
        if h : (e.symm k).val < cols - t then
          f (finHeadEquiv ht ⟨e.symm k, h⟩) else 0)
      = ∑ u : Fin (cols - t), f u := by
  classical
  let g : Fin cols → M := fun j =>
    if h : j.val < cols - t then f (finHeadEquiv ht ⟨j, h⟩) else 0
  calc
    (∑ k : Fin cols,
        if h : (e.symm k).val < cols - t then
          f (finHeadEquiv ht ⟨e.symm k, h⟩) else 0)
        = ∑ k : Fin cols, g (e.symm k) := rfl
    _ = ∑ j : Fin cols, g j := by
          simpa using (Equiv.sum_comp e.symm g)
    _ = ∑ u : Fin (cols - t), f u := by
          simpa [g] using finHeadEquiv_sum_embed ht f

lemma filter_one_eq_filter_not_two {cols : Nat} {c : Fin cols → Nat}
    (hc : ∀ k, c k = 1 ∨ c k = 2) :
    ((Finset.univ : Finset (Fin cols)).filter fun k => c k = 1) =
      ((Finset.univ : Finset (Fin cols)).filter fun k => ¬ c k = 2) := by
  ext k
  rcases hc k with h | h <;> simp [h]

lemma card_filter_one_of_one_two {cols : Nat} {c : Fin cols → Nat}
    (hc : ∀ k, c k = 1 ∨ c k = 2) :
    ((Finset.univ : Finset (Fin cols)).filter fun k => c k = 1).card =
      cols - ((Finset.univ : Finset (Fin cols)).filter fun k => c k = 2).card := by
  classical
  rw [filter_one_eq_filter_not_two hc]
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin cols))) (p := fun k => c k = 2)
  have hcard :
      ((Finset.univ : Finset (Fin cols)).filter fun k => c k = 2).card
        ≤ cols := by
    simpa [Fintype.card_fin] using
      Finset.card_filter_le (s := (Finset.univ : Finset (Fin cols)))
        (p := fun k => c k = 2)
  simp [Fintype.card_fin] at h
  omega

lemma card_subtype_eq_filter {cols : Nat}
    (p : Fin cols → Prop) [DecidablePred p] :
    Fintype.card {k : Fin cols // p k} =
      ((Finset.univ : Finset (Fin cols)).filter p).card := by
  rw [Fintype.card_subtype]

lemma sum_one_two_eq_card_add_filter_two {α : Type*} [Fintype α]
    (f : α → Nat) (hf : ∀ x, f x = 1 ∨ f x = 2) :
    (∑ x : α, f x) =
      Fintype.card α + ((Finset.univ : Finset α).filter fun x => f x = 2).card := by
  classical
  have hpoint :
      ∀ x : α, f x = 1 + if f x = 2 then 1 else 0 := by
    intro x
    rcases hf x with h | h <;> simp [h]
  calc
    (∑ x : α, f x)
        = ∑ x : α, (1 + if f x = 2 then 1 else 0) := by
          exact Finset.sum_congr rfl (by intro x _; exact hpoint x)
    _ = (∑ _x : α, 1) + ∑ x : α, (if f x = 2 then 1 else 0) := by
          rw [Finset.sum_add_distrib]
    _ = (Finset.univ : Finset α).card +
        ((Finset.univ : Finset α).filter fun x => f x = 2).card := by
          have hone :
              (∑ _x : α, (1 : Nat)) = (Finset.univ : Finset α).card := by
            simp
          have htwo :
              (∑ x : α, (if f x = 2 then 1 else 0 : Nat)) =
                ((Finset.univ : Finset α).filter fun x => f x = 2).card := by
            change
              (∑ x ∈ (Finset.univ : Finset α),
                (if f x = 2 then 1 else 0 : Nat)) =
                  ((Finset.univ : Finset α).filter fun x => f x = 2).card
            exact Finset.sum_boole (fun x : α => f x = 2)
              (Finset.univ : Finset α)
          rw [hone, htwo]
    _ = Fintype.card α + ((Finset.univ : Finset α).filter fun x => f x = 2).card := by
          rw [Finset.card_univ]

theorem sum_qge2LayeredRowTargetNat_eq_of_one_two {m r : Nat}
    (hm2 : 2 ≤ m)
    (a epsBit : Fin (m + m) → Nat) (c : Fin ((m + m) - 1) → Nat)
    (ha : ∀ i, a i = 1 ∨ a i = 2)
    (heps : ∀ i, epsBit i = 0 ∨ epsBit i = 1)
    (hc : ∀ k, c k = 1 ∨ c k = 2)
    (heps_sum : (∑ i : Fin (m + m), epsBit i) = r)
    (ha_eq_c :
      (∑ i : Fin (m + m), a i) =
        (∑ k : Fin ((m + m) - 1), c k)) :
    (∑ i : Fin (m + m),
        (qge2LayeredRowTargetNat (m + m) r a epsBit i : Int)) =
      2 * ((m + m - 1 : Nat) : Int) * (m + m : Int)
        - ((m + m - 1
            + ((Finset.univ : Finset (Fin ((m + m) - 1))).filter
                fun k => c k = 2).card : Nat) : Int) := by
  classical
  have hsumc : (∑ k : Fin ((m + m) - 1), c k) =
      ((m + m) - 1) +
        ((Finset.univ : Finset (Fin ((m + m) - 1))).filter
          fun k => c k = 2).card := by
    simpa [Fintype.card_fin] using
      sum_one_two_eq_card_add_filter_two c hc
  calc
    (∑ i : Fin (m + m),
        (qge2LayeredRowTargetNat (m + m) r a epsBit i : Int))
        = ∑ i : Fin (m + m),
            (qge2OrdinaryRowTarget (m + m) r a epsBit i +
              2 * (((m + m) - 1 : Nat) : Int)) := by
            apply Finset.sum_congr rfl
            intro i _
            exact qge2LayeredRowTargetNat_cast (by omega) (ha i) (heps i)
    _ = (∑ i : Fin (m + m),
            qge2OrdinaryRowTarget (m + m) r a epsBit i)
          + ∑ i : Fin (m + m),
            2 * (((m + m) - 1 : Nat) : Int) := by
            rw [Finset.sum_add_distrib]
    _ = - (∑ k : Fin ((m + m) - 1), (c k : Int))
          + 2 * (((m + m) - 1 : Nat) : Int) * (m + m : Int) := by
            rw [qge2OrdinaryRowTarget_sum_eq_neg_columnSum
              (n := m + m) (r := r) a epsBit c heps_sum ha_eq_c]
            simp [Finset.sum_const, Fintype.card_fin, mul_comm]
    _ = 2 * ((m + m - 1 : Nat) : Int) * (m + m : Int)
          - ((m + m - 1
              + ((Finset.univ : Finset (Fin ((m + m) - 1))).filter
                  fun k => c k = 2).card : Nat) : Int) := by
            have hcsumInt :
                (∑ k : Fin ((m + m) - 1), (c k : Int)) =
                  ((m + m - 1
                    + ((Finset.univ : Finset (Fin ((m + m) - 1))).filter
                        fun k => c k = 2).card : Nat) : Int) := by
              exact_mod_cast hsumc
            rw [hcsumInt]
            ring

theorem exists_qge2UniformBrow_of_five_le_half {m r : Nat}
    (hm5 : 5 ≤ m) (hrpos : 0 < r)
    (a epsBit : Fin (m + m) → Nat) (c : Fin ((m + m) - 1) → Nat)
    (ha : ∀ i, a i = 1 ∨ a i = 2)
    (heps : ∀ i, epsBit i = 0 ∨ epsBit i = 1)
    (hc : ∀ k, c k = 1 ∨ c k = 2)
    (heps_sum : (∑ i : Fin (m + m), epsBit i) = r)
    (ha_eq_c :
      (∑ i : Fin (m + m), a i) =
        (∑ k : Fin ((m + m) - 1), c k)) :
    ∃ Brow : Fin (m + m) → Nat,
      (∀ i, qge2LayeredBRowLo (m + m) r a epsBit i ≤ Brow i ∧
        Brow i ≤ qge2LayeredBRowHi (m + m) r a epsBit i) ∧
      (∑ i : Fin (m + m), Brow i) = m * ((m + m) - 1) := by
  classical
  let lo : Fin (m + m) → Nat :=
    fun i => qge2LayeredBRowLo (m + m) r a epsBit i
  let hi : Fin (m + m) → Nat :=
    fun i => qge2LayeredBRowHi (m + m) r a epsBit i
  have hle : ∀ i : Fin (m + m), lo i ≤ hi i := by
    intro i
    exact qge2LayeredBRowLo_le_hi (by omega) a epsBit i
  have hsumc : (∑ k : Fin ((m + m) - 1), c k) =
      ((m + m) - 1) +
        ((Finset.univ : Finset (Fin ((m + m) - 1))).filter
          fun k => c k = 2).card := by
    simpa [Fintype.card_fin] using
      sum_one_two_eq_card_add_filter_two c hc
  let t :=
    ((Finset.univ : Finset (Fin ((m + m) - 1))).filter fun k => c k = 2).card
  have ht : t ≤ (m + m) - 1 := by
    dsimp [t]
    simpa [Fintype.card_fin] using
      Finset.card_filter_le
        (s := (Finset.univ : Finset (Fin ((m + m) - 1))))
        (p := fun k => c k = 2)
  have hsumAint :
      ((∑ i : Fin (m + m), a i : Nat) : Int) =
        ((m + m - 1 + t : Nat) : Int) := by
    rw [ha_eq_c, hsumc]
  have hsumAintCast :
      (∑ i : Fin (m + m), (a i : Int)) =
        ((m + m - 1 + t : Nat) : Int) := by
    rw [← hsumAint]
    exact_mod_cast rfl
  have hsumEpsIntCast :
      (∑ i : Fin (m + m), (epsBit i : Int)) = (r : Int) := by
    exact_mod_cast heps_sum
  have hloTriple : (3 * (∑ i : Fin (m + m), lo i) : Int) ≤
      (m + m : Int) * (m + m : Int) + 1 - (t : Int) := by
    calc
      (3 * (∑ i : Fin (m + m), lo i) : Int)
          = ∑ i : Fin (m + m), (3 * lo i : Int) := by
              have hnat :
                  3 * (∑ i : Fin (m + m), lo i) =
                    ∑ i : Fin (m + m), 3 * lo i := by
                rw [Finset.mul_sum]
              exact_mod_cast hnat
      _ ≤ ∑ i : Fin (m + m),
            ((r : Int) + (m + m : Int)
              - (m + m : Int) * (epsBit i : Int)
              - (a i : Int) + 1) := by
              apply Finset.sum_le_sum
              intro i _
              exact qge2LayeredBRowLo_triple_le
                (by omega) hrpos (ha i) (heps i)
      _ = (m + m : Int) * (m + m : Int) + 1 - (t : Int) := by
              simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
              rw [← Finset.mul_sum]
              rw [hsumEpsIntCast, hsumAintCast]
              have hmtCast :
                  ((m + m - 1 + t : Nat) : Int) =
                    (m : Int) + (m : Int) - 1 + (t : Int) := by
                omega
              rw [hmtCast]
              ring
  have hlo : (∑ i : Fin (m + m), lo i) ≤ m * ((m + m) - 1) := by
    have htarget :
        (m + m : Int) * (m + m : Int) + 1 - (t : Int) ≤
          3 * (m * ((m + m) - 1) : Nat) := by
      have htInt : (t : Int) ≤ (m + m - 1 : Nat) := by
        exact_mod_cast ht
      have hmInt : (5 : Int) ≤ (m : Int) := by
        exact_mod_cast hm5
      have hcolsCast :
          (((m + m) - 1 : Nat) : Int) = (m : Int) + (m : Int) - 1 := by
        omega
      rw [Nat.cast_mul, hcolsCast]
      nlinarith
    have h3 : (3 * (∑ i : Fin (m + m), lo i) : Int) ≤
        3 * (m * ((m + m) - 1) : Nat) := hloTriple.trans htarget
    norm_num at h3 ⊢
    omega
  have hDsum :
      (∑ i : Fin (m + m),
        (qge2LayeredRowTargetNat (m + m) r a epsBit i : Int)) =
      2 * ((m + m - 1 : Nat) : Int) * (m + m : Int)
        - ((m + m - 1 + t : Nat) : Int) := by
    calc
      (∑ i : Fin (m + m),
          (qge2LayeredRowTargetNat (m + m) r a epsBit i : Int))
          = ∑ i : Fin (m + m),
              (qge2OrdinaryRowTarget (m + m) r a epsBit i +
                2 * (((m + m) - 1 : Nat) : Int)) := by
              apply Finset.sum_congr rfl
              intro i _
              exact qge2LayeredRowTargetNat_cast (by omega) (ha i) (heps i)
      _ = (∑ i : Fin (m + m),
              qge2OrdinaryRowTarget (m + m) r a epsBit i)
            + ∑ i : Fin (m + m),
              2 * (((m + m) - 1 : Nat) : Int) := by
              rw [Finset.sum_add_distrib]
      _ = - (∑ k : Fin ((m + m) - 1), (c k : Int))
            + 2 * (((m + m) - 1 : Nat) : Int) * (m + m : Int) := by
              rw [qge2OrdinaryRowTarget_sum_eq_neg_columnSum
                (n := m + m) (r := r) a epsBit c heps_sum ha_eq_c]
              simp [Finset.sum_const, Fintype.card_fin, mul_comm]
      _ = 2 * ((m + m - 1 : Nat) : Int) * (m + m : Int)
            - ((m + m - 1 + t : Nat) : Int) := by
              have hcsumInt :
                  (∑ k : Fin ((m + m) - 1), (c k : Int)) =
                    ((m + m - 1 + t : Nat) : Int) := by
                exact_mod_cast hsumc
              rw [hcsumInt]
              ring
  have hhiTriple :
      (3 * (m * ((m + m) - 1) : Nat) : Int) ≤
        3 * (∑ i : Fin (m + m), hi i : Nat) := by
    have hper :
        (∑ i : Fin (m + m),
          (((qge2LayeredRowTargetNat (m + m) r a epsBit i : Nat) : Int)
            - 2)) ≤
          ∑ i : Fin (m + m), 3 * (hi i : Int) := by
      apply Finset.sum_le_sum
      intro i _
      dsimp [hi]
      exact qge2LayeredBRowHi_triple_ge (n := m + m) (r := r) a epsBit i
    have hleft_eq :
        (∑ i : Fin (m + m),
          (((qge2LayeredRowTargetNat (m + m) r a epsBit i : Nat) : Int)
            - 2)) =
          (∑ i : Fin (m + m),
            (qge2LayeredRowTargetNat (m + m) r a epsBit i : Int))
            - 2 * (m + m : Int) := by
      simp [mul_comm]
    have hright_eq : (∑ i : Fin (m + m), 3 * (hi i : Int)) =
        3 * (∑ i : Fin (m + m), hi i : Nat) := by
      have hnat :
          3 * (∑ i : Fin (m + m), hi i) =
            ∑ i : Fin (m + m), 3 * hi i := by
        rw [Finset.mul_sum]
      exact_mod_cast hnat.symm
    rw [hleft_eq, hright_eq, hDsum] at hper
    have htarget :
        (3 * (m * ((m + m) - 1) : Nat) : Int) ≤
          2 * ((m + m - 1 : Nat) : Int) * (m + m : Int)
            - ((m + m - 1 + t : Nat) : Int)
            - 2 * (m + m : Int) := by
      have htInt : (t : Int) ≤ (m + m - 1 : Nat) := by
        exact_mod_cast ht
      have hmInt : (5 : Int) ≤ (m : Int) := by
        exact_mod_cast hm5
      have hcolsCast :
          (((m + m) - 1 : Nat) : Int) = (m : Int) + (m : Int) - 1 := by
        omega
      have hmtCast :
          ((m + m - 1 + t : Nat) : Int) =
            (m : Int) + (m : Int) - 1 + (t : Int) := by
        omega
      rw [Nat.cast_mul, hcolsCast, hmtCast]
      have hmnonneg : 0 ≤ (m : Int) - 5 := by omega
      have hpos : 0 ≤ 2 * (m : Int) + 1 := by omega
      have hfactor :
          0 ≤ ((m : Int) - 5) * (2 * (m : Int) + 1) :=
        mul_nonneg hmnonneg hpos
      have hquad :
          0 ≤ 2 * (m : Int) * (m : Int) - 9 * (m : Int) + 2 := by
        nlinarith
      nlinarith
    exact htarget.trans hper
  have hhi : m * ((m + m) - 1) ≤ ∑ i : Fin (m + m), hi i := by
    omega
  rcases exists_nat_between_with_sum lo hi hle hlo hhi with
    ⟨Brow, hbetween, hsum⟩
  exact ⟨Brow, hbetween, hsum⟩

theorem exists_qge2UniformBrow_of_four_half {r : Nat}
    (hrOdd : Odd r) (hrlt : r < 8) (hrpos : 0 < r)
    (a epsBit : Fin (4 + 4) → Nat) (c : Fin ((4 + 4) - 1) → Nat)
    (ha : ∀ i, a i = 1 ∨ a i = 2)
    (heps : ∀ i, epsBit i = 0 ∨ epsBit i = 1)
    (hc : ∀ k, c k = 1 ∨ c k = 2)
    (heps_sum : (∑ i : Fin (4 + 4), epsBit i) = r)
    (ha_eq_c :
      (∑ i : Fin (4 + 4), a i) =
        (∑ k : Fin ((4 + 4) - 1), c k)) :
    ∃ Brow : Fin (4 + 4) → Nat,
      (∀ i, qge2LayeredBRowLo (4 + 4) r a epsBit i ≤ Brow i ∧
        Brow i ≤ qge2LayeredBRowHi (4 + 4) r a epsBit i) ∧
      (∑ i : Fin (4 + 4), Brow i) = 4 * ((4 + 4) - 1) := by
  classical
  let lo : Fin (4 + 4) → Nat :=
    fun i => qge2LayeredBRowLo (4 + 4) r a epsBit i
  let hi : Fin (4 + 4) → Nat :=
    fun i => qge2LayeredBRowHi (4 + 4) r a epsBit i
  have hle : ∀ i : Fin (4 + 4), lo i ≤ hi i := by
    intro i
    exact qge2LayeredBRowLo_le_hi (by omega) a epsBit i
  have hsumc : (∑ k : Fin ((4 + 4) - 1), c k) =
      ((4 + 4) - 1) +
        ((Finset.univ : Finset (Fin ((4 + 4) - 1))).filter
          fun k => c k = 2).card := by
    simpa [Fintype.card_fin] using
      sum_one_two_eq_card_add_filter_two c hc
  let t :=
    ((Finset.univ : Finset (Fin ((4 + 4) - 1))).filter fun k => c k = 2).card
  have hsumAint :
      ((∑ i : Fin (4 + 4), a i : Nat) : Int) =
        (((4 + 4) - 1 + t : Nat) : Int) := by
    rw [ha_eq_c, hsumc]
  have hsumAintCast :
      (∑ i : Fin (4 + 4), (a i : Int)) =
        (((4 + 4) - 1 + t : Nat) : Int) := by
    rw [← hsumAint]
    exact_mod_cast rfl
  have hsumEpsIntCast :
      (∑ i : Fin (4 + 4), (epsBit i : Int)) = (r : Int) := by
    exact_mod_cast heps_sum
  have hloTriple : (3 * (∑ i : Fin (4 + 4), lo i) : Int) ≤
      ((4 + 4 : Nat) : Int) * ((4 + 4 : Nat) : Int) + 1 - (t : Int) := by
    calc
      (3 * (∑ i : Fin (4 + 4), lo i) : Int)
          = ∑ i : Fin (4 + 4), (3 * lo i : Int) := by
              have hnat :
                  3 * (∑ i : Fin (4 + 4), lo i) =
                    ∑ i : Fin (4 + 4), 3 * lo i := by
                rw [Finset.mul_sum]
              exact_mod_cast hnat
      _ ≤ ∑ i : Fin (4 + 4),
            ((r : Int) + ((4 + 4 : Nat) : Int)
              - ((4 + 4 : Nat) : Int) * (epsBit i : Int)
              - (a i : Int) + 1) := by
              apply Finset.sum_le_sum
              intro i _
              exact qge2LayeredBRowLo_triple_le
                (by omega) hrpos (ha i) (heps i)
      _ = ((4 + 4 : Nat) : Int) * ((4 + 4 : Nat) : Int)
            + 1 - (t : Int) := by
              simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
              rw [← Finset.mul_sum]
              rw [hsumEpsIntCast, hsumAintCast]
              rw [show (((4 + 4) - 1 + t : Nat) : Int) = 7 + (t : Int) by omega]
              ring
  have hlo : (∑ i : Fin (4 + 4), lo i) ≤ 4 * ((4 + 4) - 1) := by
    have h3 : (3 * (∑ i : Fin (4 + 4), lo i) : Int) ≤
        3 * (4 * ((4 + 4) - 1) : Nat) := by
      have htarget :
          ((4 + 4 : Nat) : Int) * ((4 + 4 : Nat) : Int)
              + 1 - (t : Int) ≤
            3 * (4 * ((4 + 4) - 1) : Nat) := by
        omega
      exact hloTriple.trans htarget
    norm_num at h3 ⊢
    omega
  have hhi : 4 * ((4 + 4) - 1) ≤ ∑ i : Fin (4 + 4), hi i := by
    have hrCases : r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7 := by
      interval_cases r
      · simp
      · exfalso
        norm_num at hrOdd
      · simp
      · exfalso
        norm_num at hrOdd
      · simp
      · exfalso
        norm_num at hrOdd
      · simp
    rcases hrCases with rfl | rfl | rfl | rfl
    · have hper :
          ∀ i : Fin (4 + 4),
            ((4 : Int) - 3 * (epsBit i : Int)) ≤ (hi i : Int) := by
        intro i
        rcases ha i with hai | hai <;> rcases heps i with hei | hei <;>
          simp [hi, qge2LayeredBRowHi, qge2LayeredRowTargetNat, hai, hei]
      have hsumEps : (∑ i : Fin (4 + 4), (epsBit i : Int)) = (1 : Int) := by
        exact_mod_cast heps_sum
      have hleft :
          (28 : Int) ≤
            ∑ i : Fin (4 + 4), ((4 : Int) - 3 * (epsBit i : Int)) := by
        calc
          (∑ i : Fin (4 + 4), ((4 : Int) - 3 * (epsBit i : Int)))
              = (∑ _i : Fin (4 + 4), (4 : Int)) -
                  ∑ i : Fin (4 + 4), 3 * (epsBit i : Int) := by
                rw [Finset.sum_sub_distrib]
          _ = 29 := by
                rw [← Finset.mul_sum, hsumEps]
                norm_num [Fintype.card_fin]
          _ ≥ 28 := by norm_num
      have hsumHi :
          (28 : Int) ≤ ∑ i : Fin (4 + 4), (hi i : Int) :=
        hleft.trans (Finset.sum_le_sum (by intro i _; exact hper i))
      exact_mod_cast hsumHi
    · have hper :
          ∀ i : Fin (4 + 4),
            ((5 : Int) - 3 * (epsBit i : Int)) ≤ (hi i : Int) := by
        intro i
        rcases ha i with hai | hai <;> rcases heps i with hei | hei <;>
          simp [hi, qge2LayeredBRowHi, qge2LayeredRowTargetNat, hai, hei]
      have hsumEps : (∑ i : Fin (4 + 4), (epsBit i : Int)) = (3 : Int) := by
        exact_mod_cast heps_sum
      have hleft :
          (28 : Int) ≤
            ∑ i : Fin (4 + 4), ((5 : Int) - 3 * (epsBit i : Int)) := by
        calc
          (∑ i : Fin (4 + 4), ((5 : Int) - 3 * (epsBit i : Int)))
              = (∑ _i : Fin (4 + 4), (5 : Int)) -
                  ∑ i : Fin (4 + 4), 3 * (epsBit i : Int) := by
                rw [Finset.sum_sub_distrib]
          _ = 31 := by
                rw [← Finset.mul_sum, hsumEps]
                norm_num [Fintype.card_fin]
          _ ≥ 28 := by norm_num
      have hsumHi :
          (28 : Int) ≤ ∑ i : Fin (4 + 4), (hi i : Int) :=
        hleft.trans (Finset.sum_le_sum (by intro i _; exact hper i))
      exact_mod_cast hsumHi
    · have hper :
          ∀ i : Fin (4 + 4),
            ((5 : Int) - 2 * (epsBit i : Int)) ≤ (hi i : Int) := by
        intro i
        rcases ha i with hai | hai <;> rcases heps i with hei | hei <;>
          simp [hi, qge2LayeredBRowHi, qge2LayeredRowTargetNat, hai, hei]
      have hsumEps : (∑ i : Fin (4 + 4), (epsBit i : Int)) = (5 : Int) := by
        exact_mod_cast heps_sum
      have hleft :
          (28 : Int) ≤
            ∑ i : Fin (4 + 4), ((5 : Int) - 2 * (epsBit i : Int)) := by
        calc
          (∑ i : Fin (4 + 4), ((5 : Int) - 2 * (epsBit i : Int)))
              = (∑ _i : Fin (4 + 4), (5 : Int)) -
                  ∑ i : Fin (4 + 4), 2 * (epsBit i : Int) := by
                rw [Finset.sum_sub_distrib]
          _ = 30 := by
                rw [← Finset.mul_sum, hsumEps]
                norm_num [Fintype.card_fin]
          _ ≥ 28 := by norm_num
      have hsumHi :
          (28 : Int) ≤ ∑ i : Fin (4 + 4), (hi i : Int) :=
        hleft.trans (Finset.sum_le_sum (by intro i _; exact hper i))
      exact_mod_cast hsumHi
    · let bonus : Fin (4 + 4) → Nat :=
        fun i => epsBit i * (2 - a i)
      have hsumc_le : (∑ k : Fin ((4 + 4) - 1), c k) ≤ 14 := by
        calc
          (∑ k : Fin ((4 + 4) - 1), c k)
              ≤ ∑ _k : Fin ((4 + 4) - 1), 2 := by
                apply Finset.sum_le_sum
                intro k _
                rcases hc k with hck | hck <;> omega
          _ = 14 := by norm_num [Fintype.card_fin]
      have hsuma_le : (∑ i : Fin (4 + 4), a i) ≤ 14 := by
        rw [ha_eq_c]
        exact hsumc_le
      have hex : ∃ i : Fin (4 + 4), epsBit i = 1 ∧ a i = 1 := by
        by_contra hno
        have hpoint : ∀ i : Fin (4 + 4), 1 + epsBit i ≤ a i := by
          intro i
          rcases heps i with hei | hei <;> rcases ha i with hai | hai
          · omega
          · omega
          · exact False.elim (hno ⟨i, hei, hai⟩)
          · omega
        have hsumlower :
            (∑ i : Fin (4 + 4), (1 + epsBit i)) ≤
              ∑ i : Fin (4 + 4), a i := by
          exact Finset.sum_le_sum (by intro i _; exact hpoint i)
        have hleft : (∑ i : Fin (4 + 4), (1 + epsBit i)) = 15 := by
          rw [Finset.sum_add_distrib, heps_sum]
          norm_num [Fintype.card_fin]
        omega
      have hbonus : 1 ≤ ∑ i : Fin (4 + 4), bonus i := by
        rcases hex with ⟨i, hei, hai⟩
        have hsingle :=
          Finset.single_le_sum
            (s := (Finset.univ : Finset (Fin (4 + 4))))
            (f := bonus) (by intro j _; exact Nat.zero_le (bonus j))
            (Finset.mem_univ i)
        simpa [bonus, hei, hai] using hsingle
      have hbonusCast :
          (∑ i : Fin (4 + 4),
              (epsBit i : Int) * (2 - (a i : Int))) =
            ∑ i : Fin (4 + 4), (bonus i : Int) := by
        apply Finset.sum_congr rfl
        intro i _
        rcases ha i with hai | hai <;> rcases heps i with hei | hei <;>
          simp [bonus, hai, hei]
      have hbonusInt : (1 : Int) ≤ ∑ i : Fin (4 + 4), (bonus i : Int) := by
        exact_mod_cast hbonus
      have hper :
          ∀ i : Fin (4 + 4),
            ((6 : Int) - 3 * (epsBit i : Int) +
              (epsBit i : Int) * (2 - (a i : Int))) ≤ (hi i : Int) := by
        intro i
        rcases ha i with hai | hai <;> rcases heps i with hei | hei <;>
          simp [hi, qge2LayeredBRowHi, qge2LayeredRowTargetNat, hai, hei]
      have hsumEps : (∑ i : Fin (4 + 4), (epsBit i : Int)) = (7 : Int) := by
        exact_mod_cast heps_sum
      have hleft :
          (28 : Int) ≤
            ∑ i : Fin (4 + 4),
              ((6 : Int) - 3 * (epsBit i : Int) +
                (epsBit i : Int) * (2 - (a i : Int))) := by
        calc
          (∑ i : Fin (4 + 4),
              ((6 : Int) - 3 * (epsBit i : Int) +
                (epsBit i : Int) * (2 - (a i : Int))))
              =
            ((∑ _i : Fin (4 + 4), (6 : Int)) -
              ∑ i : Fin (4 + 4), 3 * (epsBit i : Int)) +
                ∑ i : Fin (4 + 4),
                  (epsBit i : Int) * (2 - (a i : Int)) := by
                rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          _ = 27 + ∑ i : Fin (4 + 4), (bonus i : Int) := by
                rw [← Finset.mul_sum, hsumEps, hbonusCast]
                norm_num [Fintype.card_fin]
          _ ≥ 28 := by omega
      have hsumHi :
          (28 : Int) ≤ ∑ i : Fin (4 + 4), (hi i : Int) :=
        hleft.trans (Finset.sum_le_sum (by intro i _; exact hper i))
      exact_mod_cast hsumHi
  rcases exists_nat_between_with_sum lo hi hle hlo hhi with
    ⟨Brow, hbetween, hsum⟩
  exact ⟨Brow, hbetween, hsum⟩

theorem exists_qge2UniformBrow_of_four_le_half {m r : Nat}
    (hm4 : 4 ≤ m) (hrOdd : Odd r) (hrlt : r < m + m) (hrpos : 0 < r)
    (a epsBit : Fin (m + m) → Nat) (c : Fin ((m + m) - 1) → Nat)
    (ha : ∀ i, a i = 1 ∨ a i = 2)
    (heps : ∀ i, epsBit i = 0 ∨ epsBit i = 1)
    (hc : ∀ k, c k = 1 ∨ c k = 2)
    (heps_sum : (∑ i : Fin (m + m), epsBit i) = r)
    (ha_eq_c :
      (∑ i : Fin (m + m), a i) =
        (∑ k : Fin ((m + m) - 1), c k)) :
    ∃ Brow : Fin (m + m) → Nat,
      (∀ i, qge2LayeredBRowLo (m + m) r a epsBit i ≤ Brow i ∧
        Brow i ≤ qge2LayeredBRowHi (m + m) r a epsBit i) ∧
      (∑ i : Fin (m + m), Brow i) = m * ((m + m) - 1) := by
  by_cases hm5 : 5 ≤ m
  · exact exists_qge2UniformBrow_of_five_le_half hm5 hrpos
      a epsBit c ha heps hc heps_sum ha_eq_c
  · have hm : m = 4 := by omega
    subst m
    exact exists_qge2UniformBrow_of_four_half
      hrOdd hrlt hrpos a epsBit c ha heps hc heps_sum ha_eq_c

theorem exists_qge2C2LowBrow_of_three_half {r : Nat}
    (hrOdd : Odd r) (hrlt : r < 3 + 3) (hrpos : 0 < r)
    (a epsBit : Fin (3 + 3) → Nat) (c : Fin ((3 + 3) - 1) → Nat)
    (ha : ∀ i, a i = 1 ∨ a i = 2)
    (heps : ∀ i, epsBit i = 0 ∨ epsBit i = 1)
    (hc : ∀ k, c k = 1 ∨ c k = 2)
    (heps_sum : (∑ i : Fin (3 + 3), epsBit i) = r)
    (ha_eq_c :
      (∑ i : Fin (3 + 3), a i) =
        (∑ k : Fin ((3 + 3) - 1), c k)) :
    ∃ Brow : Fin (3 + 3) → Nat,
      (∀ i, qge2LayeredBRowLo (3 + 3) r a epsBit i ≤ Brow i ∧
        Brow i ≤ qge2LayeredBRowHi (3 + 3) r a epsBit i) ∧
      (∑ i : Fin (3 + 3), Brow i) =
        3 * ((3 + 3) - 1) -
          ((Finset.univ : Finset (Fin ((3 + 3) - 1))).filter
            fun k => c k = 2).card := by
  classical
  let lo : Fin (3 + 3) → Nat :=
    fun i => qge2LayeredBRowLo (3 + 3) r a epsBit i
  let hi : Fin (3 + 3) → Nat :=
    fun i => qge2LayeredBRowHi (3 + 3) r a epsBit i
  let t :=
    ((Finset.univ : Finset (Fin ((3 + 3) - 1))).filter fun k => c k = 2).card
  have ht : t ≤ (3 + 3) - 1 := by
    dsimp [t]
    simpa [Fintype.card_fin] using
      Finset.card_filter_le
        (s := (Finset.univ : Finset (Fin ((3 + 3) - 1))))
        (p := fun k => c k = 2)
  have htargetCast :
      ((3 * ((3 + 3) - 1) - t : Nat) : Int) = 15 - (t : Int) := by
    omega
  have hle : ∀ i : Fin (3 + 3), lo i ≤ hi i := by
    intro i
    exact qge2LayeredBRowLo_le_hi (by omega) a epsBit i
  have hsumc : (∑ k : Fin ((3 + 3) - 1), c k) =
      ((3 + 3) - 1) +
        ((Finset.univ : Finset (Fin ((3 + 3) - 1))).filter
          fun k => c k = 2).card := by
    simpa [Fintype.card_fin] using
      sum_one_two_eq_card_add_filter_two c hc
  have hsumAint :
      (∑ i : Fin (3 + 3), (a i : Int)) = 5 + (t : Int) := by
    have hsumA :
        ((∑ i : Fin (3 + 3), a i : Nat) : Int) =
          (((3 + 3) - 1 + t : Nat) : Int) := by
      rw [ha_eq_c, hsumc]
    have hcast :
        (((3 + 3) - 1 + t : Nat) : Int) = 5 + (t : Int) := by
      omega
    rw [show (∑ i : Fin (3 + 3), (a i : Int)) =
        ((∑ i : Fin (3 + 3), a i : Nat) : Int) by exact_mod_cast rfl]
    rw [hsumA, hcast]
  have hsumEpsInt :
      (∑ i : Fin (3 + 3), (epsBit i : Int)) = (r : Int) := by
    exact_mod_cast heps_sum
  have htpos : 1 ≤ t := by
    have hsumA_ge : 6 ≤ ∑ i : Fin (3 + 3), a i := by
      calc
        6 = ∑ _i : Fin (3 + 3), 1 := by
          norm_num [Fintype.card_fin]
        _ ≤ ∑ i : Fin (3 + 3), a i := by
          apply Finset.sum_le_sum
          intro i _
          rcases ha i with hai | hai <;> omega
    have hsumA_nat : (∑ i : Fin (3 + 3), a i) = 5 + t := by
      rw [ha_eq_c, hsumc]
    omega
  have hlo :
      (∑ i : Fin (3 + 3), lo i) ≤ 3 * ((3 + 3) - 1) - t := by
    have hrCases : r = 1 ∨ r = 3 ∨ r = 5 := by
      rcases hrOdd with ⟨s, hs⟩
      omega
    rcases hrCases with rfl | rfl | rfl
    · have hloInt :
          (∑ i : Fin (3 + 3), (lo i : Int)) =
            ∑ i : Fin (3 + 3), ((2 : Int) - 2 * (epsBit i : Int)) := by
        apply Finset.sum_congr rfl
        intro i _
        rcases ha i with hai | hai <;> rcases heps i with hei | hei <;>
          simp [lo, qge2LayeredBRowLo, qge2LayeredRowTargetNat, hai, hei]
      have hleInt : ((∑ i : Fin (3 + 3), lo i : Nat) : Int) ≤
          (3 * ((3 + 3) - 1) - t : Nat) := by
        rw [show ((∑ i : Fin (3 + 3), lo i : Nat) : Int) =
            ∑ i : Fin (3 + 3), (lo i : Int) by exact_mod_cast rfl]
        rw [hloInt, htargetCast]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        have hsumEps : (∑ i : Fin (3 + 3), (epsBit i : Int)) = 1 := by
          exact_mod_cast heps_sum
        rw [hsumEps]
        norm_num [Fintype.card_fin]
        omega
      exact_mod_cast hleInt
    · have hloInt :
          (∑ i : Fin (3 + 3), (lo i : Int)) =
            ∑ i : Fin (3 + 3),
              ((4 : Int) - (a i : Int) - 2 * (epsBit i : Int)) := by
        apply Finset.sum_congr rfl
        intro i _
        rcases ha i with hai | hai <;> rcases heps i with hei | hei <;>
          simp [lo, qge2LayeredBRowLo, qge2LayeredRowTargetNat, hai, hei]
      have hleInt : ((∑ i : Fin (3 + 3), lo i : Nat) : Int) ≤
          (3 * ((3 + 3) - 1) - t : Nat) := by
        rw [show ((∑ i : Fin (3 + 3), lo i : Nat) : Int) =
            ∑ i : Fin (3 + 3), (lo i : Int) by exact_mod_cast rfl]
        rw [hloInt, htargetCast]
        simp [Finset.sum_sub_distrib]
        rw [← Finset.mul_sum]
        have hsumEps : (∑ i : Fin (3 + 3), (epsBit i : Int)) = 3 := by
          exact_mod_cast heps_sum
        rw [hsumAint, hsumEps]
        norm_num [Fintype.card_fin]
        omega
      exact_mod_cast hleInt
    · have hloInt :
          (∑ i : Fin (3 + 3), (lo i : Int)) =
            ∑ i : Fin (3 + 3), ((3 : Int) - 2 * (epsBit i : Int)) := by
        apply Finset.sum_congr rfl
        intro i _
        rcases ha i with hai | hai <;> rcases heps i with hei | hei <;>
          simp [lo, qge2LayeredBRowLo, qge2LayeredRowTargetNat, hai, hei]
      have hleInt : ((∑ i : Fin (3 + 3), lo i : Nat) : Int) ≤
          (3 * ((3 + 3) - 1) - t : Nat) := by
        rw [show ((∑ i : Fin (3 + 3), lo i : Nat) : Int) =
            ∑ i : Fin (3 + 3), (lo i : Int) by exact_mod_cast rfl]
        rw [hloInt, htargetCast]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        have hsumEps : (∑ i : Fin (3 + 3), (epsBit i : Int)) = 5 := by
          exact_mod_cast heps_sum
        rw [hsumEps]
        norm_num [Fintype.card_fin]
        omega
      exact_mod_cast hleInt
  have hhi :
      3 * ((3 + 3) - 1) - t ≤ ∑ i : Fin (3 + 3), hi i := by
    have hrCases : r = 1 ∨ r = 3 ∨ r = 5 := by
      rcases hrOdd with ⟨s, hs⟩
      omega
    rcases hrCases with rfl | rfl | rfl
    · have hhiInt :
          (∑ i : Fin (3 + 3), (hi i : Int)) =
            ∑ i : Fin (3 + 3), ((3 : Int) - 2 * (epsBit i : Int)) := by
        apply Finset.sum_congr rfl
        intro i _
        rcases ha i with hai | hai <;> rcases heps i with hei | hei <;>
          simp [hi, qge2LayeredBRowHi, qge2LayeredRowTargetNat, hai, hei]
      have hleInt : ((3 * ((3 + 3) - 1) - t : Nat) : Int) ≤
          (∑ i : Fin (3 + 3), hi i : Nat) := by
        rw [show ((∑ i : Fin (3 + 3), hi i : Nat) : Int) =
            ∑ i : Fin (3 + 3), (hi i : Int) by exact_mod_cast rfl]
        rw [hhiInt, htargetCast]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        have hsumEps : (∑ i : Fin (3 + 3), (epsBit i : Int)) = 1 := by
          exact_mod_cast heps_sum
        rw [hsumEps]
        norm_num [Fintype.card_fin]
        omega
      exact_mod_cast hleInt
    · have hhiInt :
          (∑ i : Fin (3 + 3), (hi i : Int)) =
            ∑ i : Fin (3 + 3),
              ((5 : Int) - (a i : Int) - 2 * (epsBit i : Int)) := by
        apply Finset.sum_congr rfl
        intro i _
        rcases ha i with hai | hai <;> rcases heps i with hei | hei <;>
          simp [hi, qge2LayeredBRowHi, qge2LayeredRowTargetNat, hai, hei]
      have hleInt : ((3 * ((3 + 3) - 1) - t : Nat) : Int) ≤
          (∑ i : Fin (3 + 3), hi i : Nat) := by
        rw [show ((∑ i : Fin (3 + 3), hi i : Nat) : Int) =
            ∑ i : Fin (3 + 3), (hi i : Int) by exact_mod_cast rfl]
        rw [hhiInt, htargetCast]
        simp [Finset.sum_sub_distrib]
        rw [← Finset.mul_sum]
        have hsumEps : (∑ i : Fin (3 + 3), (epsBit i : Int)) = 3 := by
          exact_mod_cast heps_sum
        rw [hsumAint, hsumEps]
        norm_num [Fintype.card_fin]
        omega
      exact_mod_cast hleInt
    · have hhiInt :
          (∑ i : Fin (3 + 3), (hi i : Int)) =
            ∑ i : Fin (3 + 3), ((4 : Int) - 2 * (epsBit i : Int)) := by
        apply Finset.sum_congr rfl
        intro i _
        rcases ha i with hai | hai <;> rcases heps i with hei | hei <;>
          simp [hi, qge2LayeredBRowHi, qge2LayeredRowTargetNat, hai, hei]
      have hleInt : ((3 * ((3 + 3) - 1) - t : Nat) : Int) ≤
          (∑ i : Fin (3 + 3), hi i : Nat) := by
        rw [show ((∑ i : Fin (3 + 3), hi i : Nat) : Int) =
            ∑ i : Fin (3 + 3), (hi i : Int) by exact_mod_cast rfl]
        rw [hhiInt, htargetCast]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        have hsumEps : (∑ i : Fin (3 + 3), (epsBit i : Int)) = 5 := by
          exact_mod_cast heps_sum
        rw [hsumEps]
        norm_num [Fintype.card_fin]
        omega
      exact_mod_cast hleInt
  rcases exists_nat_between_with_sum lo hi hle hlo hhi with
    ⟨Brow, hbetween, hsum⟩
  exact ⟨Brow, hbetween, by simpa [t] using hsum⟩

noncomputable def finSplitOneTwoEquiv {cols : Nat} (c : Fin cols → Nat)
    (hc : ∀ k, c k = 1 ∨ c k = 2) :
    Fin cols ≃ ({k : Fin cols // c k = 1} ⊕ {k : Fin cols // c k = 2}) where
  toFun k :=
    if h1 : c k = 1 then Sum.inl ⟨k, h1⟩ else
      Sum.inr ⟨k, by
        rcases hc k with h | h
        · exact False.elim (h1 h)
        · exact h⟩
  invFun s := match s with
    | Sum.inl k => k.1
    | Sum.inr k => k.1
  left_inv := by
    intro k
    by_cases h1 : c k = 1 <;> simp [h1]
  right_inv := by
    intro s
    cases s with
    | inl k =>
        simp [k.2]
    | inr k =>
        have hnot : ¬ c k.1 = 1 := by
          intro h1
          omega
        simp [hnot]

noncomputable def finSplitHeadTailEquiv {cols t : Nat} (_ht : t ≤ cols) :
    Fin cols ≃
      ({j : Fin cols // j.val < cols - t} ⊕
        {j : Fin cols // cols - t ≤ j.val}) where
  toFun j :=
    if hlt : j.val < cols - t then Sum.inl ⟨j, hlt⟩ else
      Sum.inr ⟨j, by omega⟩
  invFun s := match s with
    | Sum.inl j => j.1
    | Sum.inr j => j.1
  left_inv := by
    intro j
    by_cases hlt : j.val < cols - t <;> simp [hlt]
  right_inv := by
    intro s
    cases s with
    | inl j =>
        simp [j.2]
    | inr j =>
        have hnot : ¬ j.1.val < cols - t := by omega
        simp [hnot]

theorem exists_perm_symm_tail_iff_two {cols : Nat}
    (c : Fin cols → Nat) (hc : ∀ k, c k = 1 ∨ c k = 2) :
    ∃ e : Equiv.Perm (Fin cols),
      ∀ k : Fin cols,
        (cols - ((Finset.univ : Finset (Fin cols)).filter fun k => c k = 2).card
            ≤ (e.symm k).val) ↔ c k = 2 := by
  classical
  let t := ((Finset.univ : Finset (Fin cols)).filter fun k => c k = 2).card
  have ht : t ≤ cols := by
    dsimp [t]
    simpa [Fintype.card_fin] using
      Finset.card_filter_le (s := (Finset.univ : Finset (Fin cols)))
        (p := fun k => c k = 2)
  let One := {k : Fin cols // c k = 1}
  let Two := {k : Fin cols // c k = 2}
  let Head := {j : Fin cols // j.val < cols - t}
  let Tail := {j : Fin cols // cols - t ≤ j.val}
  have hOneCard : Fintype.card One = cols - t := by
    dsimp [One, t]
    rw [card_subtype_eq_filter]
    exact card_filter_one_of_one_two hc
  have hTwoCard : Fintype.card Two = t := by
    dsimp [Two, t]
    rw [card_subtype_eq_filter]
  have hHeadCard : Fintype.card Head = cols - t := by
    dsimp [Head]
    exact (Fintype.card_congr (finHeadEquiv ht)).trans
      (Fintype.card_fin (cols - t))
  have hTailCard : Fintype.card Tail = t := by
    dsimp [Tail]
    exact (Fintype.card_congr (finTailEquiv ht)).trans
      (Fintype.card_fin t)
  let oneEquiv : One ≃ Head :=
    Fintype.equivOfCardEq (hOneCard.trans hHeadCard.symm)
  let twoEquiv : Two ≃ Tail :=
    Fintype.equivOfCardEq (hTwoCard.trans hTailCard.symm)
  let eSymm : Equiv.Perm (Fin cols) :=
    (finSplitOneTwoEquiv c hc).trans
      ((Equiv.sumCongr oneEquiv twoEquiv).trans
        (finSplitHeadTailEquiv ht).symm)
  refine ⟨eSymm.symm, ?_⟩
  intro k
  dsimp [eSymm]
  by_cases h1 : c k = 1
  · have hnot2 : c k ≠ 2 := by omega
    have hhead : ((oneEquiv ⟨k, h1⟩ : Head).1).val < cols - t :=
      (oneEquiv ⟨k, h1⟩).2
    simp [finSplitOneTwoEquiv, finSplitHeadTailEquiv, h1]
    dsimp [t] at hhead ⊢
    omega
  · have h2 : c k = 2 := by
      rcases hc k with h | h
      · exact False.elim (h1 h)
      · exact h
    have htail : cols - t ≤ ((twoEquiv ⟨k, h2⟩ : Tail).1).val :=
      (twoEquiv ⟨k, h2⟩).2
    simp [finSplitOneTwoEquiv, finSplitHeadTailEquiv, h2]
    dsimp [t] at htail ⊢
    omega

theorem qge2UniformB_Acol_eq_almost_of_tail_iff_two {m cols : Nat}
    (hm2 : 2 ≤ m) (c : Fin cols → Nat)
    (hc : ∀ k, c k = 1 ∨ c k = 2) {e : Equiv.Perm (Fin cols)}
    (he : ∀ k : Fin cols,
      (cols - ((Finset.univ : Finset (Fin cols)).filter fun k => c k = 2).card
          ≤ (e.symm k).val) ↔ c k = 2) :
    ∀ k : Fin cols,
      m - c k =
        (m - 1) -
          if cols - ((Finset.univ : Finset (Fin cols)).filter fun k => c k = 2).card
              ≤ (e.symm k).val then 1 else 0 := by
  intro k
  rcases hc k with h1 | h2
  · have htailFalse :
        ¬ cols - ((Finset.univ : Finset (Fin cols)).filter fun k => c k = 2).card
            ≤ (e.symm k).val := by
      intro htail
      have htwo := (he k).1 htail
      omega
    simp [h1, htailFalse]
  · have htail :
        cols - ((Finset.univ : Finset (Fin cols)).filter fun k => c k = 2).card
          ≤ (e.symm k).val := (he k).2 h2
    simp [h2, htail]
    omega

structure ZeroOneDegreeMatrixData (rows cols : Nat)
    (rowDeg : Fin rows → Nat) (colDeg : Fin cols → Nat) where
  G : Fin rows → Fin cols → Nat
  G_zero_one : ∀ i k, G i k = 0 ∨ G i k = 1
  G_row_sum : ∀ i : Fin rows, (∑ k : Fin cols, G i k) = rowDeg i
  G_col_sum : ∀ k : Fin cols, (∑ i : Fin rows, G i k) = colDeg k

def ZeroOneDegreeMatrixData.congrDegrees {rows cols : Nat}
    {rowDeg rowDeg' : Fin rows → Nat} {colDeg colDeg' : Fin cols → Nat}
    (D : ZeroOneDegreeMatrixData rows cols rowDeg colDeg)
    (hrow : ∀ i, rowDeg i = rowDeg' i)
    (hcol : ∀ k, colDeg k = colDeg' k) :
    ZeroOneDegreeMatrixData rows cols rowDeg' colDeg' where
  G := D.G
  G_zero_one := D.G_zero_one
  G_row_sum := by
    intro i
    rw [← hrow i]
    exact D.G_row_sum i
  G_col_sum := by
    intro k
    rw [← hcol k]
    exact D.G_col_sum k

def ZeroOneDegreeMatrixData.transpose {rows cols : Nat}
    {rowDeg : Fin rows → Nat} {colDeg : Fin cols → Nat}
    (D : ZeroOneDegreeMatrixData rows cols rowDeg colDeg) :
    ZeroOneDegreeMatrixData cols rows colDeg rowDeg where
  G := fun k i => D.G i k
  G_zero_one := by
    intro k i
    exact D.G_zero_one i k
  G_row_sum := by
    intro k
    exact D.G_col_sum k
  G_col_sum := by
    intro i
    exact D.G_row_sum i

def ZeroOneDegreeMatrixData.reindexCols {rows cols : Nat}
    {rowDeg : Fin rows → Nat} {colDeg : Fin cols → Nat}
    (D : ZeroOneDegreeMatrixData rows cols rowDeg colDeg)
    (e : Equiv.Perm (Fin cols)) :
    ZeroOneDegreeMatrixData rows cols rowDeg
      (fun k => colDeg (e.symm k)) where
  G := fun i k => D.G i (e.symm k)
  G_zero_one := by
    intro i k
    exact D.G_zero_one i (e.symm k)
  G_row_sum := by
    intro i
    calc
      (∑ k : Fin cols, D.G i (e.symm k)) =
          ∑ k : Fin cols, D.G i k := by
            simpa using
              (Equiv.sum_comp e.symm (fun k : Fin cols => D.G i k))
      _ = rowDeg i := D.G_row_sum i
  G_col_sum := by
    intro k
    exact D.G_col_sum (e.symm k)

def ZeroOneDegreeMatrixData.reindexRows {rows cols : Nat}
    {rowDeg : Fin rows → Nat} {colDeg : Fin cols → Nat}
    (D : ZeroOneDegreeMatrixData rows cols rowDeg colDeg)
    (e : Equiv.Perm (Fin rows)) :
    ZeroOneDegreeMatrixData rows cols
      (fun i => rowDeg (e.symm i)) colDeg where
  G := fun i k => D.G (e.symm i) k
  G_zero_one := by
    intro i k
    exact D.G_zero_one (e.symm i) k
  G_row_sum := by
    intro i
    exact D.G_row_sum (e.symm i)
  G_col_sum := by
    intro k
    calc
      (∑ i : Fin rows, D.G (e.symm i) k) =
          ∑ i : Fin rows, D.G i k := by
            simpa using
              (Equiv.sum_comp e.symm (fun i : Fin rows => D.G i k))
      _ = colDeg k := D.G_col_sum k

def ZeroOneDegreeMatrixData.complement {rows cols : Nat}
    {rowDeg : Fin rows → Nat} {colDeg : Fin cols → Nat}
    (D : ZeroOneDegreeMatrixData rows cols rowDeg colDeg) :
    ZeroOneDegreeMatrixData rows cols
      (fun i => cols - rowDeg i) (fun k => rows - colDeg k) where
  G := fun i k => 1 - D.G i k
  G_zero_one := by
    intro i k
    rcases D.G_zero_one i k with h | h <;> simp [h]
  G_row_sum := by
    intro i
    have hrowLe : rowDeg i ≤ cols := by
      rw [← D.G_row_sum i]
      calc
        (∑ k : Fin cols, D.G i k)
            ≤ ∑ _k : Fin cols, 1 := by
              apply Finset.sum_le_sum
              intro k _
              rcases D.G_zero_one i k with h | h <;> simp [h]
        _ = cols := by simp [Fintype.card_fin]
    have hInt : ((∑ k : Fin cols, (1 - D.G i k : Nat)) : Int) =
        ((cols - rowDeg i : Nat) : Int) := by
      rw [Nat.cast_sub hrowLe]
      calc
        (∑ k : Fin cols, (1 - D.G i k : Nat) : Int)
            = ∑ k : Fin cols, ((1 : Int) - (D.G i k : Int)) := by
              apply Finset.sum_congr rfl
              intro k _
              rcases D.G_zero_one i k with h | h <;> simp [h]
        _ = (cols : Int) - ∑ k : Fin cols, (D.G i k : Int) := by
              simp [Finset.sum_sub_distrib, Fintype.card_fin]
        _ = (cols : Int) - (rowDeg i : Int) := by
              rw [show (∑ k : Fin cols, (D.G i k : Int)) =
                  (rowDeg i : Int) by exact_mod_cast D.G_row_sum i]
    exact_mod_cast hInt
  G_col_sum := by
    intro k
    have hcolLe : colDeg k ≤ rows := by
      rw [← D.G_col_sum k]
      calc
        (∑ i : Fin rows, D.G i k)
            ≤ ∑ _i : Fin rows, 1 := by
              apply Finset.sum_le_sum
              intro i _
              rcases D.G_zero_one i k with h | h <;> simp [h]
        _ = rows := by simp [Fintype.card_fin]
    have hInt : ((∑ i : Fin rows, (1 - D.G i k : Nat)) : Int) =
        ((rows - colDeg k : Nat) : Int) := by
      rw [Nat.cast_sub hcolLe]
      calc
        (∑ i : Fin rows, (1 - D.G i k : Nat) : Int)
            = ∑ i : Fin rows, ((1 : Int) - (D.G i k : Int)) := by
              apply Finset.sum_congr rfl
              intro i _
              rcases D.G_zero_one i k with h | h <;> simp [h]
        _ = (rows : Int) - ∑ i : Fin rows, (D.G i k : Int) := by
              simp [Finset.sum_sub_distrib, Fintype.card_fin]
        _ = (rows : Int) - (colDeg k : Int) := by
              rw [show (∑ i : Fin rows, (D.G i k : Int)) =
                  (colDeg k : Int) by exact_mod_cast D.G_col_sum k]
    exact_mod_cast hInt

noncomputable def ZeroOneDegreeMatrixData.glueHeadTailReindex {rows cols t : Nat}
    {headRow tailRow : Fin rows → Nat}
    {headCol : Fin (cols - t) → Nat} {tailCol : Fin t → Nat}
    (ht : t ≤ cols) (e : Equiv.Perm (Fin cols))
    (Head : ZeroOneDegreeMatrixData rows (cols - t) headRow headCol)
    (Tail : ZeroOneDegreeMatrixData rows t tailRow tailCol) :
    ZeroOneDegreeMatrixData rows cols
      (fun i => headRow i + tailRow i)
      (fun k =>
        if htail : cols - t ≤ (e.symm k).val then
          tailCol (finTailEquiv ht ⟨e.symm k, htail⟩)
        else
          headCol (finHeadEquiv ht ⟨e.symm k, by omega⟩)) where
  G := fun i k =>
    if htail : cols - t ≤ (e.symm k).val then
      Tail.G i (finTailEquiv ht ⟨e.symm k, htail⟩)
    else
      Head.G i (finHeadEquiv ht ⟨e.symm k, by omega⟩)
  G_zero_one := by
    intro i k
    by_cases htail : cols - t ≤ (e.symm k).val
    · simpa [htail] using
        Tail.G_zero_one i (finTailEquiv ht ⟨e.symm k, htail⟩)
    · simpa [htail] using
        Head.G_zero_one i (finHeadEquiv ht ⟨e.symm k, by omega⟩)
  G_row_sum := by
    intro i
    have hpoint :
        (fun k : Fin cols =>
          if htail : cols - t ≤ (e.symm k).val then
            Tail.G i (finTailEquiv ht ⟨e.symm k, htail⟩)
          else
            Head.G i (finHeadEquiv ht ⟨e.symm k, by omega⟩))
          =
        (fun k : Fin cols =>
          (if htail : cols - t ≤ (e.symm k).val then
            Tail.G i (finTailEquiv ht ⟨e.symm k, htail⟩) else 0) +
          (if hhead : (e.symm k).val < cols - t then
            Head.G i (finHeadEquiv ht ⟨e.symm k, hhead⟩) else 0)) := by
      funext k
      by_cases htail : cols - t ≤ (e.symm k).val
      · have hheadFalse : ¬ (e.symm k).val < cols - t := by omega
        simp [htail, hheadFalse]
      · have hhead : (e.symm k).val < cols - t := by omega
        simp [htail, hhead]
    calc
      (∑ k : Fin cols,
        (if htail : cols - t ≤ (e.symm k).val then
          Tail.G i (finTailEquiv ht ⟨e.symm k, htail⟩)
        else
          Head.G i (finHeadEquiv ht ⟨e.symm k, by omega⟩)))
          =
        ∑ k : Fin cols,
          ((if htail : cols - t ≤ (e.symm k).val then
            Tail.G i (finTailEquiv ht ⟨e.symm k, htail⟩) else 0) +
          (if hhead : (e.symm k).val < cols - t then
            Head.G i (finHeadEquiv ht ⟨e.symm k, hhead⟩) else 0)) := by
            rw [hpoint]
      _ =
        (∑ k : Fin cols,
          if htail : cols - t ≤ (e.symm k).val then
            Tail.G i (finTailEquiv ht ⟨e.symm k, htail⟩) else 0) +
        (∑ k : Fin cols,
          if hhead : (e.symm k).val < cols - t then
            Head.G i (finHeadEquiv ht ⟨e.symm k, hhead⟩) else 0) := by
            rw [Finset.sum_add_distrib]
      _ = tailRow i + headRow i := by
            rw [finTailEquiv_sum_embed_perm ht e (fun u => Tail.G i u),
              finHeadEquiv_sum_embed_perm ht e (fun u => Head.G i u),
              Tail.G_row_sum i, Head.G_row_sum i]
      _ = headRow i + tailRow i := by omega
  G_col_sum := by
    intro k
    by_cases htail : cols - t ≤ (e.symm k).val
    · simp [htail, Tail.G_col_sum]
    · have hhead : (e.symm k).val < cols - t := by omega
      simp [htail, Head.G_col_sum]

theorem exists_uniformColumnDegreeZeroOneMatrix
    {rows cols h : Nat} (rowDegree : Fin rows → Nat)
    (hcols : 0 < cols)
    (hrowLe : ∀ i : Fin rows, rowDegree i ≤ cols)
    (htotal : (∑ i : Fin rows, rowDegree i) = h * cols) :
    Nonempty (ZeroOneDegreeMatrixData rows cols rowDegree (fun _ => h)) := by
  rcases uniformColumnDegreeMatrixGoal rowDegree hcols hrowLe htotal with ⟨D⟩
  exact ⟨{
    G := D.G
    G_zero_one := D.G_zero_one
    G_row_sum := D.G_row_sum
    G_col_sum := by
      intro k
      exact D.G_col_sum k
  }⟩

theorem exists_zeroColumnDegreeZeroOneMatrix {rows : Nat}
    {rowDegree : Fin rows → Nat} {colDegree : Fin 0 → Nat}
    (hrowZero : ∀ i : Fin rows, rowDegree i = 0) :
    Nonempty (ZeroOneDegreeMatrixData rows 0 rowDegree colDegree) := by
  refine ⟨{
    G := fun _ k => Fin.elim0 k
    G_zero_one := by
      intro _ k
      exact Fin.elim0 k
    G_row_sum := by
      intro i
      simp [hrowZero i]
    G_col_sum := by
      intro k
      exact Fin.elim0 k
  }⟩

theorem exists_c2LowBaseExtraRowMatrices_of_six_rows {t : Nat}
    (htpos : 1 ≤ t) (htle : t ≤ 5)
    (A : Fin (3 + 3) → Nat)
    (hAle : ∀ i, A i ≤ 5)
    (hAsum : (∑ i : Fin (3 + 3), A i) = 10 + 2 * t) :
    ∃ Base Extra : Fin (3 + 3) → Nat,
      Nonempty (ZeroOneDegreeMatrixData (3 + 3) ((3 + 3) - 1)
        Base (fun _ => 2)) ∧
      Nonempty (ZeroOneDegreeMatrixData (3 + 3) t
        Extra (fun _ => 2)) ∧
      (∀ i, Base i + Extra i = A i) := by
  classical
  rcases exists_c2LowExtraRowSplit_of_six_rows htpos htle A hAle hAsum with
    ⟨Extra, hExtra, hExtraSum⟩
  let Base : Fin (3 + 3) → Nat := fun i => A i - Extra i
  have hBaseLe : ∀ i : Fin (3 + 3), Base i ≤ (3 + 3) - 1 := by
    intro i
    dsimp [Base]
    exact (Nat.sub_le (A i) (Extra i)).trans (by simpa using hAle i)
  have hBaseSum : (∑ i : Fin (3 + 3), Base i) = 10 := by
    have hInt : ((∑ i : Fin (3 + 3), Base i : Nat) : Int) = 10 := by
      rw [show ((∑ i : Fin (3 + 3), Base i : Nat) : Int) =
          ∑ i : Fin (3 + 3), (Base i : Int) by exact_mod_cast rfl]
      calc
        (∑ i : Fin (3 + 3), (Base i : Int))
            = ∑ i : Fin (3 + 3), ((A i : Int) - (Extra i : Int)) := by
              apply Finset.sum_congr rfl
              intro i _
              dsimp [Base]
              rw [Nat.cast_sub (hExtra i).1]
        _ = (∑ i : Fin (3 + 3), (A i : Int)) -
              ∑ i : Fin (3 + 3), (Extra i : Int) := by
              rw [Finset.sum_sub_distrib]
        _ = 10 := by
              have hAInt :
                  (∑ i : Fin (3 + 3), (A i : Int)) =
                    (10 + 2 * t : Nat) := by
                exact_mod_cast hAsum
              have hExtraInt :
                  (∑ i : Fin (3 + 3), (Extra i : Int)) =
                    (2 * t : Nat) := by
                exact_mod_cast hExtraSum
              rw [hAInt, hExtraInt]
              omega
    exact_mod_cast hInt
  have hExtraLe : ∀ i : Fin (3 + 3), Extra i ≤ t := by
    intro i
    exact (hExtra i).2
  refine ⟨Base, Extra, ?_, ?_, ?_⟩
  · exact exists_uniformColumnDegreeZeroOneMatrix
      (rows := 3 + 3) (cols := (3 + 3) - 1) (h := 2)
      Base (by omega) hBaseLe (by simpa using hBaseSum)
  · exact exists_uniformColumnDegreeZeroOneMatrix
      (rows := 3 + 3) (cols := t) (h := 2)
      Extra (by omega) hExtraLe (by simpa [mul_comm] using hExtraSum)
  · intro i
    dsimp [Base]
    have hEiA := (hExtra i).1
    omega

theorem exists_c2LowHeadTailAData_of_six_rows {t : Nat}
    (c : Fin ((3 + 3) - 1) → Nat)
    (hc : ∀ k, c k = 1 ∨ c k = 2)
    (htcard :
      t = ((Finset.univ : Finset (Fin ((3 + 3) - 1))).filter
        fun k => c k = 2).card)
    (htpos : 1 ≤ t)
    (A L H : Fin (3 + 3) → Nat)
    (hLle : ∀ i, L i ≤ ((3 + 3) - 1) - t)
    (hHle : ∀ i, H i ≤ t)
    (hLsum : (∑ i : Fin (3 + 3), L i) =
      2 * (((3 + 3) - 1) - t))
    (hHsum : (∑ i : Fin (3 + 3), H i) = 2 * t)
    (hAeq : ∀ i, L i + (t - H i) = A i) :
    Nonempty (ZeroOneDegreeMatrixData (3 + 3) ((3 + 3) - 1)
      A (fun k => if c k = 2 then 4 else 2)) := by
  classical
  have ht : t ≤ ((3 + 3) - 1) := by
    rw [htcard]
    simpa [Fintype.card_fin] using
      Finset.card_filter_le
        (s := (Finset.univ : Finset (Fin ((3 + 3) - 1))))
        (p := fun k => c k = 2)
  have hHeadData :
      Nonempty (ZeroOneDegreeMatrixData (3 + 3) (((3 + 3) - 1) - t)
        L (fun _ : Fin (((3 + 3) - 1) - t) => 2)) := by
    by_cases hheadpos : 0 < ((3 + 3) - 1) - t
    · exact exists_uniformColumnDegreeZeroOneMatrix
        (rows := 3 + 3) (cols := ((3 + 3) - 1) - t) (h := 2)
        L hheadpos hLle (by simpa [mul_comm] using hLsum)
    · have hheadZero : ((3 + 3) - 1) - t = 0 := by omega
      have hLzero : ∀ i : Fin (3 + 3), L i = 0 := by
        intro i
        have hLi := hLle i
        omega
      rw [hheadZero]
      exact exists_zeroColumnDegreeZeroOneMatrix
        (rowDegree := L) (colDegree := fun _ : Fin 0 => 2) hLzero
  have hTailHoleData :
      Nonempty (ZeroOneDegreeMatrixData (3 + 3) t
        H (fun _ : Fin t => 2)) := by
    exact exists_uniformColumnDegreeZeroOneMatrix
      (rows := 3 + 3) (cols := t) (h := 2)
      H (by omega) hHle (by simpa [mul_comm] using hHsum)
  rcases hHeadData with ⟨Head⟩
  rcases hTailHoleData with ⟨Hole⟩
  rcases exists_perm_symm_tail_iff_two c hc with ⟨e, he⟩
  have he_t :
      ∀ k : Fin ((3 + 3) - 1),
        (((3 + 3) - 1) - t ≤ (e.symm k).val) ↔ c k = 2 := by
    intro k
    rw [htcard]
    exact he k
  let Tail := Hole.complement
  let Glued :=
    ZeroOneDegreeMatrixData.glueHeadTailReindex
      (rows := 3 + 3) (cols := (3 + 3) - 1) (t := t)
      ht e Head Tail
  exact ⟨Glued.congrDegrees
    (by
      intro i
      exact hAeq i)
    (by
      intro k
      by_cases htail : ((3 + 3) - 1) - t ≤ (e.symm k).val
      · have hck : c k = 2 := (he_t k).1 htail
        simp [htail, hck]
      · have hck : c k ≠ 2 := by
          intro h2
          exact htail ((he_t k).2 h2)
        simp [htail, hck])⟩

theorem exists_c2LowHeadTailRowSplit_of_six_rows {t : Nat}
    (htle : t ≤ ((3 + 3) - 1))
    (A : Fin (3 + 3) → Nat)
    (hAle : ∀ i, A i ≤ ((3 + 3) - 1))
    (hAsum : (∑ i : Fin (3 + 3), A i) = 10 + 2 * t)
    (hlo :
      (∑ i : Fin (3 + 3), (A i - t)) ≤
        2 * (((3 + 3) - 1) - t))
    (hhi :
      2 * (((3 + 3) - 1) - t) ≤
        ∑ i : Fin (3 + 3), min (((3 + 3) - 1) - t) (A i)) :
    ∃ L H : Fin (3 + 3) → Nat,
      (∀ i, L i ≤ ((3 + 3) - 1) - t) ∧
      (∀ i, H i ≤ t) ∧
      (∑ i : Fin (3 + 3), L i) =
        2 * (((3 + 3) - 1) - t) ∧
      (∑ i : Fin (3 + 3), H i) = 2 * t ∧
      (∀ i, L i + (t - H i) = A i) := by
  classical
  let lo : Fin (3 + 3) → Nat := fun i => A i - t
  let hi : Fin (3 + 3) → Nat :=
    fun i => min (((3 + 3) - 1) - t) (A i)
  have hle : ∀ i, lo i ≤ hi i := by
    intro i
    dsimp [lo, hi]
    apply le_min
    · have hAi := hAle i
      omega
    · exact Nat.sub_le (A i) t
  rcases exists_nat_between_with_sum lo hi hle
      (by simpa [lo] using hlo) (by simpa [hi] using hhi) with
    ⟨L, hLbetween, hLsum⟩
  let H : Fin (3 + 3) → Nat := fun i => t + L i - A i
  have hLle : ∀ i, L i ≤ ((3 + 3) - 1) - t := by
    intro i
    exact (hLbetween i).2.trans (Nat.min_le_left _ _)
  have hLleA : ∀ i, L i ≤ A i := by
    intro i
    exact (hLbetween i).2.trans (Nat.min_le_right _ _)
  have hAle_tL : ∀ i, A i ≤ t + L i := by
    intro i
    have hlow := (hLbetween i).1
    dsimp [lo] at hlow
    omega
  have hHle : ∀ i, H i ≤ t := by
    intro i
    dsimp [H]
    have hLA := hLleA i
    omega
  have hHsum : (∑ i : Fin (3 + 3), H i) = 2 * t := by
    have hInt : ((∑ i : Fin (3 + 3), H i : Nat) : Int) = (2 * t : Nat) := by
      rw [show ((∑ i : Fin (3 + 3), H i : Nat) : Int) =
          ∑ i : Fin (3 + 3), (H i : Int) by exact_mod_cast rfl]
      calc
        (∑ i : Fin (3 + 3), (H i : Int))
            = ∑ i : Fin (3 + 3),
                ((t : Int) + (L i : Int) - (A i : Int)) := by
              apply Finset.sum_congr rfl
              intro i _
              dsimp [H]
              rw [Nat.cast_sub (hAle_tL i), Nat.cast_add]
        _ =
            (∑ _i : Fin (3 + 3), (t : Int)) +
              ∑ i : Fin (3 + 3), (L i : Int) -
              ∑ i : Fin (3 + 3), (A i : Int) := by
              simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = (2 * t : Nat) := by
              have hLsumInt :
                  (∑ i : Fin (3 + 3), (L i : Int)) =
                    (2 * (((3 + 3) - 1) - t) : Nat) := by
                exact_mod_cast hLsum
              have hAsumInt :
                  (∑ i : Fin (3 + 3), (A i : Int)) =
                    (10 + 2 * t : Nat) := by
                exact_mod_cast hAsum
              rw [hLsumInt, hAsumInt]
              norm_num [Fintype.card_fin]
              omega
    exact_mod_cast hInt
  refine ⟨L, H, hLle, hHle, hLsum, hHsum, ?_⟩
  intro i
  dsimp [H]
  have hLA := hLleA i
  have hAtL := hAle_tL i
  omega

theorem exists_c2LowHeadTailAData_of_six_rows_of_bounds {t : Nat}
    (c : Fin ((3 + 3) - 1) → Nat)
    (hc : ∀ k, c k = 1 ∨ c k = 2)
    (htcard :
      t = ((Finset.univ : Finset (Fin ((3 + 3) - 1))).filter
        fun k => c k = 2).card)
    (htpos : 1 ≤ t)
    (A : Fin (3 + 3) → Nat)
    (hAle : ∀ i, A i ≤ ((3 + 3) - 1))
    (hAsum : (∑ i : Fin (3 + 3), A i) = 10 + 2 * t)
    (hlo :
      (∑ i : Fin (3 + 3), (A i - t)) ≤
        2 * (((3 + 3) - 1) - t))
    (hhi :
      2 * (((3 + 3) - 1) - t) ≤
        ∑ i : Fin (3 + 3), min (((3 + 3) - 1) - t) (A i)) :
    Nonempty (ZeroOneDegreeMatrixData (3 + 3) ((3 + 3) - 1)
      A (fun k => if c k = 2 then 4 else 2)) := by
  classical
  have ht : t ≤ ((3 + 3) - 1) := by
    rw [htcard]
    simpa [Fintype.card_fin] using
      Finset.card_filter_le
        (s := (Finset.univ : Finset (Fin ((3 + 3) - 1))))
        (p := fun k => c k = 2)
  rcases exists_c2LowHeadTailRowSplit_of_six_rows
      ht A hAle hAsum hlo hhi with
    ⟨L, H, hLle, hHle, hLsum, hHsum, hAeq⟩
  exact exists_c2LowHeadTailAData_of_six_rows
    c hc htcard htpos A L H hLle hHle hLsum hHsum hAeq

def qge2SixOdd (r : Fin 3) : Nat := 2 * r.val + 1

def boolNat (b : Bool) : Nat := if b then 1 else 0

def qge2SixAVal (a2 : Bool) : Nat := if a2 then 2 else 1

def qge2SixEpsVal (eps1 : Bool) : Nat := if eps1 then 1 else 0

def qge2SixRowTarget (r : Fin 3) (a2 eps1 : Bool) : Nat :=
  qge2SixOdd r + 2 * ((3 + 3) - 1) -
    qge2SixAVal a2 - (3 + 3) * qge2SixEpsVal eps1

def qge2SixBLoOfD (D : Nat) : Nat :=
  if D ≤ ((3 + 3) - 1) then 0 else (D - ((3 + 3) - 1) + 2) / 3

def qge2SixBHiOfD (D : Nat) : Nat := D / 3

def qge2SixBLo (r : Fin 3) (a2 eps1 : Bool) : Nat :=
  qge2SixBLoOfD (qge2SixRowTarget r a2 eps1)

def qge2SixBHi (r : Fin 3) (a2 eps1 : Bool) : Nat :=
  qge2SixBHiOfD (qge2SixRowTarget r a2 eps1)

def qge2SixDeltaB (r : Fin 3) (a2 eps1 delta : Bool) : Nat :=
  qge2SixBLo r a2 eps1 + boolNat delta

def qge2SixDeltaA (r : Fin 3) (a2 eps1 delta : Bool) : Nat :=
  qge2SixRowTarget r a2 eps1 - 3 * qge2SixDeltaB r a2 eps1 delta

def qge2SixTailCount (a2 : Fin (3 + 3) → Bool) : Nat :=
  1 + ∑ i : Fin (3 + 3), boolNat (a2 i)

def qge2SixDeltaTableProp : Prop :=
  ∀ (r : Fin 3) (a2 eps1 : Fin (3 + 3) → Bool),
    (∑ i : Fin (3 + 3), qge2SixEpsVal (eps1 i)) = qge2SixOdd r →
    qge2SixTailCount a2 ≤ ((3 + 3) - 1) →
    ∃ delta : Fin (3 + 3) → Bool,
      (∀ i : Fin (3 + 3),
        qge2SixBLo r (a2 i) (eps1 i) ≤
          qge2SixDeltaB r (a2 i) (eps1 i) (delta i) ∧
        qge2SixDeltaB r (a2 i) (eps1 i) (delta i) ≤
          qge2SixBHi r (a2 i) (eps1 i)) ∧
      (∀ i : Fin (3 + 3),
        qge2SixDeltaA r (a2 i) (eps1 i) (delta i) ≤
          ((3 + 3) - 1)) ∧
      (∑ i : Fin (3 + 3),
        qge2SixDeltaB r (a2 i) (eps1 i) (delta i)) =
          3 * ((3 + 3) - 1) - qge2SixTailCount a2 ∧
      (∑ i : Fin (3 + 3),
        qge2SixDeltaA r (a2 i) (eps1 i) (delta i)) =
          10 + 2 * qge2SixTailCount a2 ∧
      (∑ i : Fin (3 + 3),
        (qge2SixDeltaA r (a2 i) (eps1 i) (delta i) -
          qge2SixTailCount a2)) ≤
          2 * (((3 + 3) - 1) - qge2SixTailCount a2) ∧
      2 * (((3 + 3) - 1) - qge2SixTailCount a2) ≤
        ∑ i : Fin (3 + 3),
          min (((3 + 3) - 1) - qge2SixTailCount a2)
            (qge2SixDeltaA r (a2 i) (eps1 i) (delta i))

set_option linter.style.nativeDecide false in
theorem qge2SixDeltaTable : qge2SixDeltaTableProp := by
  unfold qge2SixDeltaTableProp
  native_decide

def qge2FourOdd (r : Fin 2) : Nat := 2 * r.val + 1

def qge2FourOrdRowTarget (r : Fin 2) (a2 eps1 : Bool) : Int :=
  (qge2FourOdd r : Int) - (qge2SixAVal a2 : Int) -
    (2 + 2 : Int) * (qge2SixEpsVal eps1 : Int)

def qge2FourPatternOne (p : Fin 28) (i : Fin (2 + 2)) : Int :=
  match p.val, i.val with
  | 0, 0 => (-2 : Int) | 0, 1 => (-2 : Int) | 0, 2 => (1 : Int) | 0, 3 => (2 : Int)
  | 1, 0 => (-2 : Int) | 1, 1 => (-2 : Int) | 1, 2 => (2 : Int) | 1, 3 => (1 : Int)
  | 2, 0 => (-2 : Int) | 2, 1 => (-1 : Int) | 2, 2 => (1 : Int) | 2, 3 => (1 : Int)
  | 3, 0 => (-2 : Int) | 3, 1 => (1 : Int) | 3, 2 => (-2 : Int) | 3, 3 => (2 : Int)
  | 4, 0 => (-2 : Int) | 4, 1 => (1 : Int) | 4, 2 => (-1 : Int) | 4, 3 => (1 : Int)
  | 5, 0 => (-2 : Int) | 5, 1 => (1 : Int) | 5, 2 => (1 : Int) | 5, 3 => (-1 : Int)
  | 6, 0 => (-2 : Int) | 6, 1 => (1 : Int) | 6, 2 => (2 : Int) | 6, 3 => (-2 : Int)
  | 7, 0 => (-2 : Int) | 7, 1 => (2 : Int) | 7, 2 => (-2 : Int) | 7, 3 => (1 : Int)
  | 8, 0 => (-2 : Int) | 8, 1 => (2 : Int) | 8, 2 => (1 : Int) | 8, 3 => (-2 : Int)
  | 9, 0 => (-1 : Int) | 9, 1 => (-2 : Int) | 9, 2 => (1 : Int) | 9, 3 => (1 : Int)
  | 10, 0 => (-1 : Int) | 10, 1 => (-1 : Int) | 10, 2 => (-1 : Int) | 10, 3 => (2 : Int)
  | 11, 0 => (-1 : Int) | 11, 1 => (-1 : Int) | 11, 2 => (2 : Int) | 11, 3 => (-1 : Int)
  | 12, 0 => (-1 : Int) | 12, 1 => (1 : Int) | 12, 2 => (-2 : Int) | 12, 3 => (1 : Int)
  | 13, 0 => (-1 : Int) | 13, 1 => (1 : Int) | 13, 2 => (1 : Int) | 13, 3 => (-2 : Int)
  | 14, 0 => (-1 : Int) | 14, 1 => (2 : Int) | 14, 2 => (-1 : Int) | 14, 3 => (-1 : Int)
  | 15, 0 => (1 : Int) | 15, 1 => (-2 : Int) | 15, 2 => (-2 : Int) | 15, 3 => (2 : Int)
  | 16, 0 => (1 : Int) | 16, 1 => (-2 : Int) | 16, 2 => (-1 : Int) | 16, 3 => (1 : Int)
  | 17, 0 => (1 : Int) | 17, 1 => (-2 : Int) | 17, 2 => (1 : Int) | 17, 3 => (-1 : Int)
  | 18, 0 => (1 : Int) | 18, 1 => (-2 : Int) | 18, 2 => (2 : Int) | 18, 3 => (-2 : Int)
  | 19, 0 => (1 : Int) | 19, 1 => (-1 : Int) | 19, 2 => (-2 : Int) | 19, 3 => (1 : Int)
  | 20, 0 => (1 : Int) | 20, 1 => (-1 : Int) | 20, 2 => (1 : Int) | 20, 3 => (-2 : Int)
  | 21, 0 => (1 : Int) | 21, 1 => (1 : Int) | 21, 2 => (-2 : Int) | 21, 3 => (-1 : Int)
  | 22, 0 => (1 : Int) | 22, 1 => (1 : Int) | 22, 2 => (-1 : Int) | 22, 3 => (-2 : Int)
  | 23, 0 => (1 : Int) | 23, 1 => (2 : Int) | 23, 2 => (-2 : Int) | 23, 3 => (-2 : Int)
  | 24, 0 => (2 : Int) | 24, 1 => (-2 : Int) | 24, 2 => (-2 : Int) | 24, 3 => (1 : Int)
  | 25, 0 => (2 : Int) | 25, 1 => (-2 : Int) | 25, 2 => (1 : Int) | 25, 3 => (-2 : Int)
  | 26, 0 => (2 : Int) | 26, 1 => (-1 : Int) | 26, 2 => (-1 : Int) | 26, 3 => (-1 : Int)
  | 27, 0 => (2 : Int) | 27, 1 => (1 : Int) | 27, 2 => (-2 : Int) | 27, 3 => (-2 : Int)
  | _, _ => 0

def qge2FourPatternTwo (p : Fin 28) (i : Fin (2 + 2)) : Int :=
  match p.val, i.val with
  | 0, 0 => (-2 : Int) | 0, 1 => (-2 : Int) | 0, 2 => (1 : Int) | 0, 3 => (1 : Int)
  | 1, 0 => (-2 : Int) | 1, 1 => (-1 : Int) | 1, 2 => (-1 : Int) | 1, 3 => (2 : Int)
  | 2, 0 => (-2 : Int) | 2, 1 => (-1 : Int) | 2, 2 => (2 : Int) | 2, 3 => (-1 : Int)
  | 3, 0 => (-2 : Int) | 3, 1 => (1 : Int) | 3, 2 => (-2 : Int) | 3, 3 => (1 : Int)
  | 4, 0 => (-2 : Int) | 4, 1 => (1 : Int) | 4, 2 => (1 : Int) | 4, 3 => (-2 : Int)
  | 5, 0 => (-2 : Int) | 5, 1 => (2 : Int) | 5, 2 => (-1 : Int) | 5, 3 => (-1 : Int)
  | 6, 0 => (-1 : Int) | 6, 1 => (-2 : Int) | 6, 2 => (-1 : Int) | 6, 3 => (2 : Int)
  | 7, 0 => (-1 : Int) | 7, 1 => (-2 : Int) | 7, 2 => (2 : Int) | 7, 3 => (-1 : Int)
  | 8, 0 => (-1 : Int) | 8, 1 => (-1 : Int) | 8, 2 => (-2 : Int) | 8, 3 => (2 : Int)
  | 9, 0 => (-1 : Int) | 9, 1 => (-1 : Int) | 9, 2 => (-1 : Int) | 9, 3 => (1 : Int)
  | 10, 0 => (-1 : Int) | 10, 1 => (-1 : Int) | 10, 2 => (1 : Int) | 10, 3 => (-1 : Int)
  | 11, 0 => (-1 : Int) | 11, 1 => (-1 : Int) | 11, 2 => (2 : Int) | 11, 3 => (-2 : Int)
  | 12, 0 => (-1 : Int) | 12, 1 => (1 : Int) | 12, 2 => (-1 : Int) | 12, 3 => (-1 : Int)
  | 13, 0 => (-1 : Int) | 13, 1 => (2 : Int) | 13, 2 => (-2 : Int) | 13, 3 => (-1 : Int)
  | 14, 0 => (-1 : Int) | 14, 1 => (2 : Int) | 14, 2 => (-1 : Int) | 14, 3 => (-2 : Int)
  | 15, 0 => (1 : Int) | 15, 1 => (-2 : Int) | 15, 2 => (-2 : Int) | 15, 3 => (1 : Int)
  | 16, 0 => (1 : Int) | 16, 1 => (-2 : Int) | 16, 2 => (1 : Int) | 16, 3 => (-2 : Int)
  | 17, 0 => (1 : Int) | 17, 1 => (-1 : Int) | 17, 2 => (-1 : Int) | 17, 3 => (-1 : Int)
  | 18, 0 => (1 : Int) | 18, 1 => (1 : Int) | 18, 2 => (-2 : Int) | 18, 3 => (-2 : Int)
  | 19, 0 => (2 : Int) | 19, 1 => (-2 : Int) | 19, 2 => (-1 : Int) | 19, 3 => (-1 : Int)
  | 20, 0 => (2 : Int) | 20, 1 => (-1 : Int) | 20, 2 => (-2 : Int) | 20, 3 => (-1 : Int)
  | 21, 0 => (2 : Int) | 21, 1 => (-1 : Int) | 21, 2 => (-1 : Int) | 21, 3 => (-2 : Int)
  | _, _ => 0

def qge2FourColumnVal (c2 : Bool) (p : Fin 28) (i : Fin (2 + 2)) : Int :=
  if c2 then qge2FourPatternTwo p i else qge2FourPatternOne p i

def qge2FourColumnCodeValid (c2 : Bool) (p : Fin 28) : Prop :=
  c2 = false ∨ p.val < 22

def qge2FourColumnCodeTableProp : Prop :=
  ∀ (r : Fin 2)
    (a2 eps1 : Fin (2 + 2) → Bool)
    (c2 : Fin ((2 + 2) - 1) → Bool),
    (∑ i : Fin (2 + 2), qge2SixEpsVal (eps1 i)) = qge2FourOdd r →
    (∑ i : Fin (2 + 2), qge2SixAVal (a2 i)) =
      (∑ k : Fin ((2 + 2) - 1), qge2SixAVal (c2 k)) →
    ∃ code : Fin ((2 + 2) - 1) → Fin 28,
      (∀ k : Fin ((2 + 2) - 1), qge2FourColumnCodeValid (c2 k) (code k)) ∧
      (∀ k i, IsSignedVal (qge2FourColumnVal (c2 k) (code k) i)) ∧
      (∀ k : Fin ((2 + 2) - 1),
        (∑ i : Fin (2 + 2), qge2FourColumnVal (c2 k) (code k) i) =
          - (qge2SixAVal (c2 k) : Int)) ∧
      (∀ i : Fin (2 + 2),
        (∑ k : Fin ((2 + 2) - 1), qge2FourColumnVal (c2 k) (code k) i) =
          qge2FourOrdRowTarget r (a2 i) (eps1 i))

set_option linter.style.nativeDecide false in
theorem qge2FourColumnCodeTable : qge2FourColumnCodeTableProp := by
  unfold qge2FourColumnCodeTableProp qge2FourColumnCodeValid IsSignedVal signedVals
  native_decide

theorem qge2SixAVal_decide_eq {x : Nat} (hx : x = 1 ∨ x = 2) :
    qge2SixAVal (decide (x = 2)) = x := by
  rcases hx with rfl | rfl <;> simp [qge2SixAVal]

theorem qge2SixEpsVal_decide_eq {x : Nat} (hx : x = 0 ∨ x = 1) :
    qge2SixEpsVal (decide (x = 1)) = x := by
  rcases hx with rfl | rfl <;> simp [qge2SixEpsVal]

theorem boolNat_decide_eq_one_of_one_two {x : Nat} (hx : x = 1 ∨ x = 2) :
    boolNat (decide (x = 2)) = x - 1 := by
  rcases hx with rfl | rfl <;> simp [boolNat]

theorem qge2SixTailCount_decide_eq_filter_two
    (a : Fin (3 + 3) → Nat) :
    qge2SixTailCount (fun i : Fin (3 + 3) => decide (a i = 2)) =
      1 + ((Finset.univ : Finset (Fin (3 + 3))).filter
        fun i => a i = 2).card := by
  classical
  unfold qge2SixTailCount
  congr 1
  change
    (∑ i : Fin (3 + 3), (if decide (a i = 2) then 1 else 0)) =
      ((Finset.univ : Finset (Fin (3 + 3))).filter fun i => a i = 2).card
  simp [Finset.sum_boole]

theorem qge2SixTailCount_decide_eq_c_filter_two
    (a : Fin (3 + 3) → Nat) (c : Fin ((3 + 3) - 1) → Nat)
    (ha : ∀ i, a i = 1 ∨ a i = 2)
    (hc : ∀ k, c k = 1 ∨ c k = 2)
    (ha_eq_c :
      (∑ i : Fin (3 + 3), a i) =
        (∑ k : Fin ((3 + 3) - 1), c k)) :
    qge2SixTailCount (fun i : Fin (3 + 3) => decide (a i = 2)) =
      ((Finset.univ : Finset (Fin ((3 + 3) - 1))).filter
        fun k => c k = 2).card := by
  classical
  let ta := ((Finset.univ : Finset (Fin (3 + 3))).filter
    fun i => a i = 2).card
  let tc := ((Finset.univ : Finset (Fin ((3 + 3) - 1))).filter
    fun k => c k = 2).card
  have hsumA : (∑ i : Fin (3 + 3), a i) = (3 + 3) + ta := by
    dsimp [ta]
    simpa [Fintype.card_fin] using sum_one_two_eq_card_add_filter_two a ha
  have hsumC : (∑ k : Fin ((3 + 3) - 1), c k) =
      ((3 + 3) - 1) + tc := by
    dsimp [tc]
    simpa [Fintype.card_fin] using sum_one_two_eq_card_add_filter_two c hc
  have htailA :=
    qge2SixTailCount_decide_eq_filter_two a
  have hcardEq : (3 + 3) + ta = ((3 + 3) - 1) + tc := by
    rw [← hsumA, ha_eq_c, hsumC]
  rw [htailA]
  change 1 + ta = tc
  omega

theorem qge2SixEpsSum_decide_eq
    (epsBit : Fin (3 + 3) → Nat)
    (heps : ∀ i, epsBit i = 0 ∨ epsBit i = 1)
    {r : Nat}
    (heps_sum : (∑ i : Fin (3 + 3), epsBit i) = r) :
    (∑ i : Fin (3 + 3),
      qge2SixEpsVal (decide (epsBit i = 1))) = r := by
  calc
    (∑ i : Fin (3 + 3),
      qge2SixEpsVal (decide (epsBit i = 1)))
        = ∑ i : Fin (3 + 3), epsBit i := by
          apply Finset.sum_congr rfl
          intro i _
          exact qge2SixEpsVal_decide_eq (heps i)
    _ = r := heps_sum

theorem qge2SixRowTarget_decide_eq {r : Nat} {rf : Fin 3}
    (hrf : qge2SixOdd rf = r)
    {a eps : Nat} (ha : a = 1 ∨ a = 2) (heps : eps = 0 ∨ eps = 1) :
    qge2SixRowTarget rf (decide (a = 2)) (decide (eps = 1)) =
      qge2LayeredRowTargetNat (3 + 3) r (fun _ : Fin (3 + 3) => a)
        (fun _ : Fin (3 + 3) => eps) 0 := by
  have hodd : 2 * rf.val + 1 = r := by
    simpa [qge2SixOdd] using hrf
  rcases ha with rfl | rfl <;> rcases heps with rfl | rfl <;>
    simp [qge2SixRowTarget, qge2SixOdd, qge2SixAVal, qge2SixEpsVal,
      qge2LayeredRowTargetNat, hodd]

theorem exists_qge2C2LowRowsWithADataBounds_of_three_half {r t : Nat}
    (hrOdd : Odd r) (hrlt : r < 3 + 3) (hrpos : 0 < r)
    (a epsBit : Fin (3 + 3) → Nat) (c : Fin ((3 + 3) - 1) → Nat)
    (ha : ∀ i, a i = 1 ∨ a i = 2)
    (heps : ∀ i, epsBit i = 0 ∨ epsBit i = 1)
    (hc : ∀ k, c k = 1 ∨ c k = 2)
    (heps_sum : (∑ i : Fin (3 + 3), epsBit i) = r)
    (ha_eq_c :
      (∑ i : Fin (3 + 3), a i) =
        (∑ k : Fin ((3 + 3) - 1), c k))
    (htcard :
      t = ((Finset.univ : Finset (Fin ((3 + 3) - 1))).filter
        fun k => c k = 2).card) :
    ∃ Arow Brow : Fin (3 + 3) → Nat,
      (∀ i, qge2LayeredBRowLo (3 + 3) r a epsBit i ≤ Brow i ∧
        Brow i ≤ qge2LayeredBRowHi (3 + 3) r a epsBit i) ∧
      (∑ i : Fin (3 + 3), Brow i) = 3 * ((3 + 3) - 1) - t ∧
      (∀ i, Arow i + 3 * Brow i =
        qge2LayeredRowTargetNat (3 + 3) r a epsBit i) ∧
      (∀ i, Arow i ≤ ((3 + 3) - 1)) ∧
      (∑ i : Fin (3 + 3), Arow i) = 10 + 2 * t ∧
      (∑ i : Fin (3 + 3), (Arow i - t)) ≤
        2 * (((3 + 3) - 1) - t) ∧
      2 * (((3 + 3) - 1) - t) ≤
        ∑ i : Fin (3 + 3), min (((3 + 3) - 1) - t) (Arow i) := by
  classical
  let a2 : Fin (3 + 3) → Bool := fun i => decide (a i = 2)
  let eps1 : Fin (3 + 3) → Bool := fun i => decide (epsBit i = 1)
  have htEq : qge2SixTailCount a2 = t := by
    dsimp [a2]
    rw [qge2SixTailCount_decide_eq_c_filter_two a c ha hc ha_eq_c, ← htcard]
  have htLe : qge2SixTailCount a2 ≤ ((3 + 3) - 1) := by
    rw [htEq, htcard]
    simpa [Fintype.card_fin] using
      Finset.card_filter_le
        (s := (Finset.univ : Finset (Fin ((3 + 3) - 1))))
        (p := fun k => c k = 2)
  have hFor :
      ∀ rf : Fin 3, qge2SixOdd rf = r →
        ∃ Arow Brow : Fin (3 + 3) → Nat,
          (∀ i, qge2LayeredBRowLo (3 + 3) r a epsBit i ≤ Brow i ∧
            Brow i ≤ qge2LayeredBRowHi (3 + 3) r a epsBit i) ∧
          (∑ i : Fin (3 + 3), Brow i) = 3 * ((3 + 3) - 1) - t ∧
          (∀ i, Arow i + 3 * Brow i =
            qge2LayeredRowTargetNat (3 + 3) r a epsBit i) ∧
          (∀ i, Arow i ≤ ((3 + 3) - 1)) ∧
          (∑ i : Fin (3 + 3), Arow i) = 10 + 2 * t ∧
          (∑ i : Fin (3 + 3), (Arow i - t)) ≤
            2 * (((3 + 3) - 1) - t) ∧
          2 * (((3 + 3) - 1) - t) ≤
            ∑ i : Fin (3 + 3), min (((3 + 3) - 1) - t) (Arow i) := by
    intro rf hrf
    have hEpsTable :
        (∑ i : Fin (3 + 3), qge2SixEpsVal (eps1 i)) = qge2SixOdd rf := by
      rw [hrf]
      dsimp [eps1]
      exact qge2SixEpsSum_decide_eq epsBit heps heps_sum
    rcases qge2SixDeltaTable rf a2 eps1 hEpsTable htLe with
      ⟨delta, hBbetweenTable, hAleTable, hBsumTable, hAsumTable,
        hloTable, hhiTable⟩
    let Brow : Fin (3 + 3) → Nat :=
      fun i => qge2SixDeltaB rf (a2 i) (eps1 i) (delta i)
    let Arow : Fin (3 + 3) → Nat :=
      fun i => qge2SixDeltaA rf (a2 i) (eps1 i) (delta i)
    have hRowTarget :
        ∀ i : Fin (3 + 3),
          qge2SixRowTarget rf (a2 i) (eps1 i) =
            qge2LayeredRowTargetNat (3 + 3) r a epsBit i := by
      have hodd : 2 * rf.val + 1 = r := by
        simpa [qge2SixOdd] using hrf
      intro i
      rcases ha i with hai | hai <;> rcases heps i with hei | hei <;>
        simp [a2, eps1, qge2SixRowTarget, qge2SixOdd, qge2SixAVal,
          qge2SixEpsVal, qge2LayeredRowTargetNat, hodd, hai, hei]
    have hBLo :
        ∀ i : Fin (3 + 3),
          qge2SixBLo rf (a2 i) (eps1 i) =
            qge2LayeredBRowLo (3 + 3) r a epsBit i := by
      intro i
      unfold qge2SixBLo qge2SixBLoOfD qge2LayeredBRowLo
      rw [hRowTarget i]
    have hBHi :
        ∀ i : Fin (3 + 3),
          qge2SixBHi rf (a2 i) (eps1 i) =
            qge2LayeredBRowHi (3 + 3) r a epsBit i := by
      intro i
      unfold qge2SixBHi qge2SixBHiOfD qge2LayeredBRowHi
      rw [hRowTarget i]
    refine ⟨Arow, Brow, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      have hb := hBbetweenTable i
      dsimp [Brow]
      constructor
      · rw [← hBLo i]
        exact hb.1
      · rw [← hBHi i]
        exact hb.2
    · dsimp [Brow]
      simpa [htEq] using hBsumTable
    · intro i
      dsimp [Arow, Brow, qge2SixDeltaA]
      have hbhi : Brow i ≤ qge2LayeredBRowHi (3 + 3) r a epsBit i := by
        dsimp [Brow]
        rw [← hBHi i]
        exact (hBbetweenTable i).2
      have hleD : 3 * Brow i ≤
          qge2LayeredRowTargetNat (3 + 3) r a epsBit i := by
        exact qge2LayeredBRowHi_spec hbhi
      have hleD' :
          3 * qge2SixDeltaB rf (a2 i) (eps1 i) (delta i) ≤
            qge2SixRowTarget rf (a2 i) (eps1 i) := by
        rw [hRowTarget i]
        simpa [Brow] using hleD
      rw [← hRowTarget i]
      omega
    · intro i
      dsimp [Arow]
      exact hAleTable i
    · dsimp [Arow]
      simpa [htEq] using hAsumTable
    · dsimp [Arow]
      simpa [htEq] using hloTable
    · dsimp [Arow]
      simpa [htEq] using hhiTable
  have hrCases : r = 1 ∨ r = 3 ∨ r = 5 := by
    rcases hrOdd with ⟨s, hs⟩
    omega
  rcases hrCases with rfl | rfl | rfl
  · exact hFor ⟨0, by decide⟩ rfl
  · exact hFor ⟨1, by decide⟩ rfl
  · exact hFor ⟨2, by decide⟩ rfl

theorem exists_qge2UniformBLayerData_of_five_le_half {m r : Nat}
    (hm5 : 5 ≤ m) (hrlt : r < m + m) (hrpos : 0 < r)
    (a epsBit : Fin (m + m) → Nat) (c : Fin ((m + m) - 1) → Nat)
    (ha : ∀ i, a i = 1 ∨ a i = 2)
    (heps : ∀ i, epsBit i = 0 ∨ epsBit i = 1)
    (hc : ∀ k, c k = 1 ∨ c k = 2)
    (heps_sum : (∑ i : Fin (m + m), epsBit i) = r)
    (ha_eq_c :
      (∑ i : Fin (m + m), a i) =
        (∑ k : Fin ((m + m) - 1), c k)) :
    ∃ Brow : Fin (m + m) → Nat,
      Nonempty (ZeroOneDegreeMatrixData (m + m) ((m + m) - 1)
        Brow (fun _ => m)) ∧
      (∀ i, qge2LayeredBRowLo (m + m) r a epsBit i ≤ Brow i ∧
        Brow i ≤ qge2LayeredBRowHi (m + m) r a epsBit i) ∧
      (∑ i : Fin (m + m), Brow i) = m * ((m + m) - 1) := by
  classical
  rcases exists_qge2UniformBrow_of_five_le_half hm5 hrpos
      a epsBit c ha heps hc heps_sum ha_eq_c with
    ⟨Brow, hbetween, hsum⟩
  have hrowLe : ∀ i : Fin (m + m), Brow i ≤ (m + m) - 1 := by
    intro i
    exact (hbetween i).2.trans
      (qge2LayeredBRowHi_le_cols (by omega) hrlt i (ha i) (heps i))
  refine ⟨Brow, ?_, hbetween, hsum⟩
  exact exists_uniformColumnDegreeZeroOneMatrix Brow (by omega) hrowLe hsum

theorem exists_qge2UniformBLayerData_of_four_le_half {m r : Nat}
    (hm4 : 4 ≤ m) (hrOdd : Odd r) (hrlt : r < m + m) (hrpos : 0 < r)
    (a epsBit : Fin (m + m) → Nat) (c : Fin ((m + m) - 1) → Nat)
    (ha : ∀ i, a i = 1 ∨ a i = 2)
    (heps : ∀ i, epsBit i = 0 ∨ epsBit i = 1)
    (hc : ∀ k, c k = 1 ∨ c k = 2)
    (heps_sum : (∑ i : Fin (m + m), epsBit i) = r)
    (ha_eq_c :
      (∑ i : Fin (m + m), a i) =
        (∑ k : Fin ((m + m) - 1), c k)) :
    ∃ Brow : Fin (m + m) → Nat,
      Nonempty (ZeroOneDegreeMatrixData (m + m) ((m + m) - 1)
        Brow (fun _ => m)) ∧
      (∀ i, qge2LayeredBRowLo (m + m) r a epsBit i ≤ Brow i ∧
        Brow i ≤ qge2LayeredBRowHi (m + m) r a epsBit i) ∧
      (∑ i : Fin (m + m), Brow i) = m * ((m + m) - 1) := by
  classical
  rcases exists_qge2UniformBrow_of_four_le_half hm4 hrOdd hrlt hrpos
      a epsBit c ha heps hc heps_sum ha_eq_c with
    ⟨Brow, hbetween, hsum⟩
  have hrowLe : ∀ i : Fin (m + m), Brow i ≤ (m + m) - 1 := by
    intro i
    exact (hbetween i).2.trans
      (qge2LayeredBRowHi_le_cols (by omega) hrlt i (ha i) (heps i))
  refine ⟨Brow, ?_, hbetween, hsum⟩
  exact exists_uniformColumnDegreeZeroOneMatrix Brow (by omega) hrowLe hsum

theorem exists_almostUniformColumnDegreeZeroOneMatrix
    {rows cols h drop : Nat} (rowDegree : Fin rows → Nat)
    (hcols : 0 < cols) (hh : 0 < h)
    (hdrop : drop ≤ cols)
    (hrowLe : ∀ i : Fin rows, rowDegree i ≤ cols)
    (htotal : (∑ i : Fin rows, rowDegree i) = h * cols - drop) :
    Nonempty (ZeroOneDegreeMatrixData rows cols rowDegree
      (fun k : Fin cols => h - if cols - drop ≤ k.val then 1 else 0)) := by
  rcases exists_almostUniformColumnDegreeMatrix rowDegree hcols hh hdrop hrowLe htotal with
    ⟨G, hG01, hGrow, hGcol⟩
  exact ⟨{
    G := G
    G_zero_one := hG01
    G_row_sum := hGrow
    G_col_sum := hGcol
  }⟩

theorem exists_almostUniformColumnDegreeZeroOneMatrix_reindex
    {rows cols h drop : Nat} (rowDegree : Fin rows → Nat)
    (e : Equiv.Perm (Fin cols))
    (hcols : 0 < cols) (hh : 0 < h)
    (hdrop : drop ≤ cols)
    (hrowLe : ∀ i : Fin rows, rowDegree i ≤ cols)
    (htotal : (∑ i : Fin rows, rowDegree i) = h * cols - drop) :
    Nonempty (ZeroOneDegreeMatrixData rows cols rowDegree
      (fun k : Fin cols =>
        h - if cols - drop ≤ (e.symm k).val then 1 else 0)) := by
  rcases exists_almostUniformColumnDegreeZeroOneMatrix rowDegree
      hcols hh hdrop hrowLe htotal with ⟨D⟩
  exact ⟨D.reindexCols e⟩

theorem exists_qge2C2LowBLayerData_of_three_half_Brow {r : Nat}
    (hrlt : r < 3 + 3)
    (a epsBit : Fin (3 + 3) → Nat) (c : Fin ((3 + 3) - 1) → Nat)
    (ha : ∀ i, a i = 1 ∨ a i = 2)
    (heps : ∀ i, epsBit i = 0 ∨ epsBit i = 1)
    (hc : ∀ k, c k = 1 ∨ c k = 2)
    (Brow : Fin (3 + 3) → Nat)
    (hbetween :
      ∀ i, qge2LayeredBRowLo (3 + 3) r a epsBit i ≤ Brow i ∧
        Brow i ≤ qge2LayeredBRowHi (3 + 3) r a epsBit i)
    (hsum :
      (∑ i : Fin (3 + 3), Brow i) =
        3 * ((3 + 3) - 1) -
          ((Finset.univ : Finset (Fin ((3 + 3) - 1))).filter
            fun k => c k = 2).card) :
    ∃ Bcol : Fin ((3 + 3) - 1) → Nat,
      Nonempty (ZeroOneDegreeMatrixData (3 + 3) ((3 + 3) - 1)
        Brow Bcol) ∧
      (∀ k, Bcol k = 3 - if c k = 2 then 1 else 0) := by
  classical
  let t :=
    ((Finset.univ : Finset (Fin ((3 + 3) - 1))).filter fun k => c k = 2).card
  have ht : t ≤ (3 + 3) - 1 := by
    dsimp [t]
    simpa [Fintype.card_fin] using
      Finset.card_filter_le
        (s := (Finset.univ : Finset (Fin ((3 + 3) - 1))))
        (p := fun k => c k = 2)
  have hrowLe : ∀ i : Fin (3 + 3), Brow i ≤ (3 + 3) - 1 := by
    intro i
    exact (hbetween i).2.trans
      (qge2LayeredBRowHi_le_cols (by omega) hrlt i (ha i) (heps i))
  rcases exists_perm_symm_tail_iff_two c hc with ⟨e, he⟩
  let Bcol : Fin ((3 + 3) - 1) → Nat := fun k =>
    3 - if (3 + 3) - 1 - t ≤ (e.symm k).val then 1 else 0
  have hBdata :
      Nonempty (ZeroOneDegreeMatrixData (3 + 3) ((3 + 3) - 1)
        Brow Bcol) := by
    dsimp [Bcol]
    exact exists_almostUniformColumnDegreeZeroOneMatrix_reindex
      (rows := 3 + 3) (cols := (3 + 3) - 1) (h := 3) (drop := t)
      Brow e (by omega) (by omega) ht hrowLe (by simpa [t] using hsum)
  refine ⟨Bcol, hBdata, ?_⟩
  intro k
  dsimp [Bcol, t]
  by_cases htail :
      (3 + 3) - 1 -
        ((Finset.univ : Finset (Fin ((3 + 3) - 1))).filter
          fun k => c k = 2).card ≤
        (e.symm k).val
  · have hck : c k = 2 := (he k).1 htail
    simp [htail, hck]
  · have hck : c k ≠ 2 := by
      intro h2
      exact htail ((he k).2 h2)
    simp [htail, hck]

theorem exists_qge2C2LowBLayerData_of_three_half {r : Nat}
    (hrOdd : Odd r) (hrlt : r < 3 + 3) (hrpos : 0 < r)
    (a epsBit : Fin (3 + 3) → Nat) (c : Fin ((3 + 3) - 1) → Nat)
    (ha : ∀ i, a i = 1 ∨ a i = 2)
    (heps : ∀ i, epsBit i = 0 ∨ epsBit i = 1)
    (hc : ∀ k, c k = 1 ∨ c k = 2)
    (heps_sum : (∑ i : Fin (3 + 3), epsBit i) = r)
    (ha_eq_c :
      (∑ i : Fin (3 + 3), a i) =
        (∑ k : Fin ((3 + 3) - 1), c k)) :
    ∃ Brow : Fin (3 + 3) → Nat,
    ∃ Bcol : Fin ((3 + 3) - 1) → Nat,
      Nonempty (ZeroOneDegreeMatrixData (3 + 3) ((3 + 3) - 1)
        Brow Bcol) ∧
      (∀ i, qge2LayeredBRowLo (3 + 3) r a epsBit i ≤ Brow i ∧
        Brow i ≤ qge2LayeredBRowHi (3 + 3) r a epsBit i) ∧
      (∀ k, Bcol k = 3 - if c k = 2 then 1 else 0) := by
  classical
  rcases exists_qge2C2LowBrow_of_three_half
      hrOdd hrlt hrpos a epsBit c ha heps hc heps_sum ha_eq_c with
    ⟨Brow, hbetween, hsum⟩
  let t :=
    ((Finset.univ : Finset (Fin ((3 + 3) - 1))).filter fun k => c k = 2).card
  have ht : t ≤ (3 + 3) - 1 := by
    dsimp [t]
    simpa [Fintype.card_fin] using
      Finset.card_filter_le
        (s := (Finset.univ : Finset (Fin ((3 + 3) - 1))))
        (p := fun k => c k = 2)
  have hrowLe : ∀ i : Fin (3 + 3), Brow i ≤ (3 + 3) - 1 := by
    intro i
    exact (hbetween i).2.trans
      (qge2LayeredBRowHi_le_cols (by omega) hrlt i (ha i) (heps i))
  rcases exists_perm_symm_tail_iff_two c hc with ⟨e, he⟩
  let Bcol : Fin ((3 + 3) - 1) → Nat := fun k =>
    3 - if (3 + 3) - 1 - t ≤ (e.symm k).val then 1 else 0
  have hBdata :
      Nonempty (ZeroOneDegreeMatrixData (3 + 3) ((3 + 3) - 1)
        Brow Bcol) := by
    dsimp [Bcol]
    exact exists_almostUniformColumnDegreeZeroOneMatrix_reindex
      (rows := 3 + 3) (cols := (3 + 3) - 1) (h := 3) (drop := t)
      Brow e (by omega) (by omega) ht hrowLe (by simpa [t] using hsum)
  refine ⟨Brow, Bcol, hBdata, hbetween, ?_⟩
  intro k
  dsimp [Bcol, t]
  by_cases htail :
      (3 + 3) - 1 -
        ((Finset.univ : Finset (Fin ((3 + 3) - 1))).filter
          fun k => c k = 2).card ≤
        (e.symm k).val
  · have hck : c k = 2 := (he k).1 htail
    simp [htail, hck]
  · have hck : c k ≠ 2 := by
      intro h2
      exact htail ((he k).2 h2)
    simp [htail, hck]

theorem exists_qge2C2LowBinaryLayerDegreeData_of_three_half {r : Nat}
    (hrOdd : Odd r) (hrlt : r < 3 + 3) (hrpos : 0 < r)
    (a epsBit : Fin (3 + 3) → Nat) (c : Fin ((3 + 3) - 1) → Nat)
    (ha : ∀ i, a i = 1 ∨ a i = 2)
    (heps : ∀ i, epsBit i = 0 ∨ epsBit i = 1)
    (hc : ∀ k, c k = 1 ∨ c k = 2)
    (heps_sum : (∑ i : Fin (3 + 3), epsBit i) = r)
    (ha_eq_c :
      (∑ i : Fin (3 + 3), a i) =
        (∑ k : Fin ((3 + 3) - 1), c k)) :
    ∃ Arow Brow : Fin (3 + 3) → Nat,
    ∃ Acol Bcol : Fin ((3 + 3) - 1) → Nat,
      Nonempty (ZeroOneDegreeMatrixData (3 + 3) ((3 + 3) - 1) Arow Acol) ∧
      Nonempty (ZeroOneDegreeMatrixData (3 + 3) ((3 + 3) - 1) Brow Bcol) ∧
      (∀ k : Fin ((3 + 3) - 1),
        (Acol k : Int) + 3 * (Bcol k : Int) =
          2 * (((3 + 3) : Nat) : Int) - (c k : Int)) ∧
      (∀ i : Fin (3 + 3),
        (Arow i : Int) + 3 * (Brow i : Int) =
          qge2OrdinaryRowTarget (3 + 3) r a epsBit i +
            2 * ((((3 + 3) - 1) : Nat) : Int)) := by
  classical
  let t :=
    ((Finset.univ : Finset (Fin ((3 + 3) - 1))).filter fun k => c k = 2).card
  have htcard :
      t = ((Finset.univ : Finset (Fin ((3 + 3) - 1))).filter
        fun k => c k = 2).card := rfl
  have htpos : 1 ≤ t := by
    have hsumA_ge : 6 ≤ ∑ i : Fin (3 + 3), a i := by
      calc
        6 = ∑ _i : Fin (3 + 3), 1 := by
          norm_num [Fintype.card_fin]
        _ ≤ ∑ i : Fin (3 + 3), a i := by
          apply Finset.sum_le_sum
          intro i _
          rcases ha i with hai | hai <;> omega
    have hsumc : (∑ k : Fin ((3 + 3) - 1), c k) =
        ((3 + 3) - 1) + t := by
      dsimp [t]
      simpa [Fintype.card_fin] using sum_one_two_eq_card_add_filter_two c hc
    have hsumA : (∑ i : Fin (3 + 3), a i) = ((3 + 3) - 1) + t := by
      rw [ha_eq_c, hsumc]
    omega
  rcases exists_qge2C2LowRowsWithADataBounds_of_three_half
      hrOdd hrlt hrpos a epsBit c ha heps hc heps_sum ha_eq_c htcard with
    ⟨Arow, Brow, hBbetween, hBsum, hRowEq, hAle, hAsum, hlo, hhi⟩
  rcases exists_qge2C2LowBLayerData_of_three_half_Brow
      hrlt a epsBit c ha heps hc Brow hBbetween
      (by simpa [t] using hBsum) with
    ⟨Bcol, hBdata, hBcol⟩
  let Acol : Fin ((3 + 3) - 1) → Nat := fun k => if c k = 2 then 4 else 2
  have hAdata :
      Nonempty (ZeroOneDegreeMatrixData (3 + 3) ((3 + 3) - 1)
        Arow Acol) := by
    dsimp [Acol]
    exact exists_c2LowHeadTailAData_of_six_rows_of_bounds
      c hc htcard htpos Arow hAle hAsum hlo hhi
  refine ⟨Arow, Brow, Acol, Bcol, hAdata, hBdata, ?_, ?_⟩
  · intro k
    dsimp [Acol]
    have hBk := hBcol k
    rcases hc k with hck | hck
    · rw [hBk]
      simp [hck]
    · rw [hBk]
      simp [hck]
  · intro i
    have hEqInt : (Arow i : Int) + 3 * (Brow i : Int) =
        (qge2LayeredRowTargetNat (3 + 3) r a epsBit i : Int) := by
      exact_mod_cast hRowEq i
    rw [hEqInt, qge2LayeredRowTargetNat_cast (by omega) (ha i) (heps i)]

theorem exists_qge2UniformBinaryLayerDegreeData_of_four_le_half {m r : Nat}
    (hm4 : 4 ≤ m) (hrOdd : Odd r) (hrlt : r < m + m) (hrpos : 0 < r)
    (a epsBit : Fin (m + m) → Nat) (c : Fin ((m + m) - 1) → Nat)
    (ha : ∀ i, a i = 1 ∨ a i = 2)
    (heps : ∀ i, epsBit i = 0 ∨ epsBit i = 1)
    (hc : ∀ k, c k = 1 ∨ c k = 2)
    (heps_sum : (∑ i : Fin (m + m), epsBit i) = r)
    (ha_eq_c :
      (∑ i : Fin (m + m), a i) =
        (∑ k : Fin ((m + m) - 1), c k)) :
    ∃ Arow Brow : Fin (m + m) → Nat,
    ∃ Acol Bcol : Fin ((m + m) - 1) → Nat,
      Nonempty (ZeroOneDegreeMatrixData (m + m) ((m + m) - 1) Arow Acol) ∧
      Nonempty (ZeroOneDegreeMatrixData (m + m) ((m + m) - 1) Brow Bcol) ∧
      (∀ k : Fin ((m + m) - 1),
        (Acol k : Int) + 3 * (Bcol k : Int) =
          2 * ((m + m : Nat) : Int) - (c k : Int)) ∧
      (∀ i : Fin (m + m),
        (Arow i : Int) + 3 * (Brow i : Int) =
          qge2OrdinaryRowTarget (m + m) r a epsBit i +
            2 * ((((m + m) - 1) : Nat) : Int)) := by
  classical
  rcases exists_qge2UniformBLayerData_of_four_le_half hm4 hrOdd hrlt hrpos
      a epsBit c ha heps hc heps_sum ha_eq_c with
    ⟨Brow, hBdata, hBbetween, hBsum⟩
  let split : ∀ i : Fin (m + m), ∃ A : Nat, A ≤ (m + m) - 1 ∧
      A + 3 * Brow i = qge2LayeredRowTargetNat (m + m) r a epsBit i := by
    intro i
    exact exists_qge2LayeredRowTargetNat_split_of_B_between
      (hBbetween i).1 (hBbetween i).2
  let Arow : Fin (m + m) → Nat := fun i => Classical.choose (split i)
  have hArowLe : ∀ i : Fin (m + m), Arow i ≤ (m + m) - 1 := by
    intro i
    exact (Classical.choose_spec (split i)).1
  have hArowEq : ∀ i : Fin (m + m),
      Arow i + 3 * Brow i = qge2LayeredRowTargetNat (m + m) r a epsBit i := by
    intro i
    exact (Classical.choose_spec (split i)).2
  let t :=
    ((Finset.univ : Finset (Fin ((m + m) - 1))).filter fun k => c k = 2).card
  have ht : t ≤ (m + m) - 1 := by
    dsimp [t]
    simpa [Fintype.card_fin] using
      Finset.card_filter_le
        (s := (Finset.univ : Finset (Fin ((m + m) - 1))))
        (p := fun k => c k = 2)
  have hDsum := sum_qge2LayeredRowTargetNat_eq_of_one_two
    (m := m) (r := r) (by omega) a epsBit c ha heps hc heps_sum ha_eq_c
  have hsumEq :
      (∑ i : Fin (m + m), (Arow i : Int))
          + 3 * (∑ i : Fin (m + m), (Brow i : Int)) =
        ∑ i : Fin (m + m),
          (qge2LayeredRowTargetNat (m + m) r a epsBit i : Int) := by
    calc
      (∑ i : Fin (m + m), (Arow i : Int))
          + 3 * (∑ i : Fin (m + m), (Brow i : Int))
          = ∑ i : Fin (m + m),
              ((Arow i : Int) + 3 * (Brow i : Int)) := by
              simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ i : Fin (m + m),
            (qge2LayeredRowTargetNat (m + m) r a epsBit i : Int) := by
              apply Finset.sum_congr rfl
              intro i _
              exact_mod_cast hArowEq i
  have hBsumInt : (∑ i : Fin (m + m), (Brow i : Int)) =
      (m * ((m + m) - 1) : Nat) := by
    exact_mod_cast hBsum
  have hArowSumInt : (∑ i : Fin (m + m), (Arow i : Int)) =
      (((m - 1) * ((m + m) - 1) - t : Nat) : Int) := by
    rw [hBsumInt, hDsum] at hsumEq
    have hcolsCast :
        (((m + m) - 1 : Nat) : Int) = (m : Int) + (m : Int) - 1 := by
      omega
    have hmtCast :
        ((m + m - 1 + t : Nat) : Int) =
          (m : Int) + (m : Int) - 1 + (t : Int) := by
      omega
    have htargetLe : t ≤ (m - 1) * ((m + m) - 1) := by
      exact ht.trans (Nat.le_mul_of_pos_left _ (by omega))
    have htargetCast :
        (((m - 1) * ((m + m) - 1) - t : Nat) : Int) =
          ((m : Int) - 1) * ((m : Int) + (m : Int) - 1) - (t : Int) := by
      rw [Nat.cast_sub htargetLe, Nat.cast_mul]
      have hpredCast : ((m - 1 : Nat) : Int) = (m : Int) - 1 := by
        omega
      rw [hpredCast, hcolsCast]
    rw [hcolsCast, hmtCast, Nat.cast_mul] at hsumEq
    rw [htargetCast]
    nlinarith
  have hArowSum : (∑ i : Fin (m + m), Arow i) =
      (m - 1) * ((m + m) - 1) - t := by
    exact_mod_cast hArowSumInt
  rcases exists_perm_symm_tail_iff_two c hc with ⟨e, he⟩
  let Acol : Fin ((m + m) - 1) → Nat := fun k =>
    (m - 1) - if (m + m) - 1 - t ≤ (e.symm k).val then 1 else 0
  let Bcol : Fin ((m + m) - 1) → Nat := fun _ => m
  have hAdata :
      Nonempty (ZeroOneDegreeMatrixData (m + m) ((m + m) - 1) Arow Acol) := by
    dsimp [Acol]
    exact exists_almostUniformColumnDegreeZeroOneMatrix_reindex
      (rows := m + m) (cols := (m + m) - 1) (h := m - 1) (drop := t)
      Arow e (by omega) (by omega) ht hArowLe hArowSum
  refine ⟨Arow, Brow, Acol, Bcol, hAdata, ?_, ?_, ?_⟩
  · simpa [Bcol] using hBdata
  · intro k
    have hAcol : Acol k = m - c k := by
      dsimp [Acol, t]
      exact (qge2UniformB_Acol_eq_almost_of_tail_iff_two (m := m)
        (cols := (m + m) - 1) (by omega) c hc he k).symm
    rw [hAcol]
    dsimp [Bcol]
    exact qge2LayeredColumnTarget_uniformB_split_int
      (m := m) (c := c k) (by omega) (hc k)
  · intro i
    have hEqInt : (Arow i : Int) + 3 * (Brow i : Int) =
        (qge2LayeredRowTargetNat (m + m) r a epsBit i : Int) := by
      exact_mod_cast hArowEq i
    rw [hEqInt, qge2LayeredRowTargetNat_cast (by omega) (ha i) (heps i)]

theorem exists_qge2BinaryLayerDegreeData_of_eight_le {n r : Nat}
    (hnEven : Even n) (hn8 : 8 ≤ n) (hrOdd : Odd r)
    (hrlt : r < n) (hrpos : 0 < r)
    (a epsBit : Fin n → Nat) (c : Fin (n - 1) → Nat)
    (ha : ∀ i, a i = 1 ∨ a i = 2)
    (heps : ∀ i, epsBit i = 0 ∨ epsBit i = 1)
    (hc : ∀ k, c k = 1 ∨ c k = 2)
    (heps_sum : (∑ i : Fin n, epsBit i) = r)
    (ha_eq_c : (∑ i : Fin n, a i) = (∑ k : Fin (n - 1), c k)) :
    ∃ Arow Brow : Fin n → Nat,
    ∃ Acol Bcol : Fin (n - 1) → Nat,
      Nonempty (ZeroOneDegreeMatrixData n (n - 1) Arow Acol) ∧
      Nonempty (ZeroOneDegreeMatrixData n (n - 1) Brow Bcol) ∧
      (∀ k : Fin (n - 1),
        (Acol k : Int) + 3 * (Bcol k : Int) =
          2 * (n : Int) - (c k : Int)) ∧
      (∀ i : Fin n,
        (Arow i : Int) + 3 * (Brow i : Int) =
          qge2OrdinaryRowTarget n r a epsBit i +
            2 * ((n - 1 : Nat) : Int)) := by
  rcases hnEven with ⟨m, rfl⟩
  exact exists_qge2UniformBinaryLayerDegreeData_of_four_le_half
    (m := m) (r := r) (by omega) hrOdd hrlt hrpos
    a epsBit c ha heps hc heps_sum ha_eq_c

theorem exists_uniformRowDegreeZeroOneMatrix
    {rows cols h : Nat} (colDegree : Fin cols → Nat)
    (hrows : 0 < rows)
    (hcolLe : ∀ k : Fin cols, colDegree k ≤ rows)
    (htotal : (∑ k : Fin cols, colDegree k) = h * rows) :
    Nonempty (ZeroOneDegreeMatrixData rows cols (fun _ => h) colDegree) := by
  rcases exists_uniformColumnDegreeZeroOneMatrix colDegree
      hrows hcolLe htotal with ⟨D⟩
  exact ⟨D.transpose⟩

theorem exists_almostUniformRowDegreeZeroOneMatrix
    {rows cols h drop : Nat} (colDegree : Fin cols → Nat)
    (hrows : 0 < rows) (hh : 0 < h)
    (hdrop : drop ≤ rows)
    (hcolLe : ∀ k : Fin cols, colDegree k ≤ rows)
    (htotal : (∑ k : Fin cols, colDegree k) = h * rows - drop) :
    Nonempty (ZeroOneDegreeMatrixData rows cols
      (fun i : Fin rows => h - if rows - drop ≤ i.val then 1 else 0)
      colDegree) := by
  rcases exists_almostUniformColumnDegreeZeroOneMatrix colDegree
      hrows hh hdrop hcolLe htotal with ⟨D⟩
  exact ⟨D.transpose⟩

theorem exists_almostUniformRowDegreeZeroOneMatrix_reindex
    {rows cols h drop : Nat} (colDegree : Fin cols → Nat)
    (e : Equiv.Perm (Fin rows))
    (hrows : 0 < rows) (hh : 0 < h)
    (hdrop : drop ≤ rows)
    (hcolLe : ∀ k : Fin cols, colDegree k ≤ rows)
    (htotal : (∑ k : Fin cols, colDegree k) = h * rows - drop) :
    Nonempty (ZeroOneDegreeMatrixData rows cols
      (fun i : Fin rows =>
        h - if rows - drop ≤ (e.symm i).val then 1 else 0)
      colDegree) := by
  rcases exists_almostUniformRowDegreeZeroOneMatrix colDegree
      hrows hh hdrop hcolLe htotal with ⟨D⟩
  exact ⟨D.reindexRows e⟩

/--
Binary-layer form of the remaining q>=2 signed trellis integrality problem.

Every signed entry is represented as `-2 + A + 3B`, where `A` and `B` are
zero-one layers.  This keeps the hard work in finite binary matrix form while
preserving exactly the ordinary-row/full-support hypotheses.
-/
def OrdinaryQge2BinaryLayerTrellisGoal : Prop :=
  ∀ {n r : Nat},
    Even n → 4 ≤ n → Odd r → r < n → 0 < r →
    ∀ (a : Fin n → Nat) (epsBit : Fin n → Nat) (c : Fin (n - 1) → Nat),
      (∀ i : Fin n, a i = 1 ∨ a i = 2) →
      (∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1) →
      (∀ k : Fin (n - 1), c k = 1 ∨ c k = 2) →
      (∑ i : Fin n, epsBit i) = r →
      (∑ i : Fin n, a i) = (∑ k : Fin (n - 1), c k) →
      (∀ w : Fin n → Int,
        (∑ i : Fin n, w i * qge2OrdinaryRowTarget n r a epsBit i)
          ≤ ∑ k : Fin (n - 1), qge2SignedColumnSupport n (c k) w) →
      ∃ A B : Fin n → Fin (n - 1) → Nat,
        (∀ i k, A i k = 0 ∨ A i k = 1) ∧
        (∀ i k, B i k = 0 ∨ B i k = 1) ∧
        (∀ k : Fin (n - 1),
          (∑ i : Fin n, ((A i k : Int) + 3 * (B i k : Int)))
            = 2 * (n : Int) - (c k : Int)) ∧
        (∀ i : Fin n,
          (∑ k : Fin (n - 1), ((A i k : Int) + 3 * (B i k : Int)))
            =
          qge2OrdinaryRowTarget n r a epsBit i
            + 2 * ((n - 1 : Nat) : Int))

def OrdinaryQge2BinaryLayerDegreeGoal : Prop :=
  ∀ {n r : Nat},
    Even n → 4 ≤ n → Odd r → r < n → 0 < r →
    ∀ (a : Fin n → Nat) (epsBit : Fin n → Nat) (c : Fin (n - 1) → Nat),
      (∀ i : Fin n, a i = 1 ∨ a i = 2) →
      (∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1) →
      (∀ k : Fin (n - 1), c k = 1 ∨ c k = 2) →
      (∑ i : Fin n, epsBit i) = r →
      (∑ i : Fin n, a i) = (∑ k : Fin (n - 1), c k) →
      (∀ w : Fin n → Int,
        (∑ i : Fin n, w i * qge2OrdinaryRowTarget n r a epsBit i)
          ≤ ∑ k : Fin (n - 1), qge2SignedColumnSupport n (c k) w) →
      ∃ Arow Brow : Fin n → Nat,
      ∃ Acol Bcol : Fin (n - 1) → Nat,
        Nonempty (ZeroOneDegreeMatrixData n (n - 1) Arow Acol) ∧
        Nonempty (ZeroOneDegreeMatrixData n (n - 1) Brow Bcol) ∧
        (∀ k : Fin (n - 1),
          (Acol k : Int) + 3 * (Bcol k : Int) =
            2 * (n : Int) - (c k : Int)) ∧
        (∀ i : Fin n,
          (Arow i : Int) + 3 * (Brow i : Int) =
            qge2OrdinaryRowTarget n r a epsBit i +
              2 * ((n - 1 : Nat) : Int))

theorem exists_qge2SignedFullSupportTrellisWitness_of_binaryLayerDegreeData
    {n r : Nat} {a epsBit : Fin n → Nat} {c : Fin (n - 1) → Nat}
    (hDegree :
      ∃ Arow Brow : Fin n → Nat,
      ∃ Acol Bcol : Fin (n - 1) → Nat,
        Nonempty (ZeroOneDegreeMatrixData n (n - 1) Arow Acol) ∧
        Nonempty (ZeroOneDegreeMatrixData n (n - 1) Brow Bcol) ∧
        (∀ k : Fin (n - 1),
          (Acol k : Int) + 3 * (Bcol k : Int) =
            2 * (n : Int) - (c k : Int)) ∧
        (∀ i : Fin n,
          (Arow i : Int) + 3 * (Brow i : Int) =
            qge2OrdinaryRowTarget n r a epsBit i +
              2 * ((n - 1 : Nat) : Int))) :
    ∃ X : Fin (n - 1) → Fin n → Int,
      (∀ k i, IsSignedVal (X k i)) ∧
      (∀ k : Fin (n - 1), (∑ i : Fin n, X k i) = - (c k : Int)) ∧
      (∀ i : Fin n,
        (∑ k : Fin (n - 1), X k i) =
          qge2OrdinaryRowTarget n r a epsBit i) := by
  classical
  rcases hDegree with
    ⟨Arow, Brow, Acol, Bcol, hAdata, hBdata, hCol, hRow⟩
  rcases hAdata with ⟨Adata⟩
  rcases hBdata with ⟨Bdata⟩
  refine ⟨fun k i => qge2LayeredSignedEntry (Adata.G i k) (Bdata.G i k), ?_, ?_, ?_⟩
  · intro k i
    exact qge2LayeredSignedEntry_isSigned
      (Adata.G_zero_one i k) (Bdata.G_zero_one i k)
  · intro k
    have hsumA :
        (∑ i : Fin n, (Adata.G i k : Int)) = (Acol k : Int) := by
      exact_mod_cast Adata.G_col_sum k
    have hsumB :
        (∑ i : Fin n, (Bdata.G i k : Int)) = (Bcol k : Int) := by
      exact_mod_cast Bdata.G_col_sum k
    have hsumB3 :
        (∑ i : Fin n, 3 * (Bdata.G i k : Int)) =
          3 * (Bcol k : Int) := by
      rw [← Finset.mul_sum, hsumB]
    have hsum :
        (∑ i : Fin n, qge2LayeredSignedEntry (Adata.G i k) (Bdata.G i k))
          =
        (∑ i : Fin n, ((Adata.G i k : Int) + 3 * (Bdata.G i k : Int)))
          - 2 * (n : Int) := by
      simp [qge2LayeredSignedEntry, Finset.sum_add_distrib,
        Finset.sum_const, Fintype.card_fin, mul_comm]
      ring
    rw [hsum]
    calc
      (∑ i : Fin n, ((Adata.G i k : Int) + 3 * (Bdata.G i k : Int)))
          - 2 * (n : Int)
          = ((Acol k : Int) + 3 * (Bcol k : Int)) - 2 * (n : Int) := by
            rw [Finset.sum_add_distrib, hsumA, hsumB3]
      _ = - (c k : Int) := by
            rw [hCol k]
            ring
  · intro i
    have hsumA :
        (∑ k : Fin (n - 1), (Adata.G i k : Int)) =
          (Arow i : Int) := by
      exact_mod_cast Adata.G_row_sum i
    have hsumB :
        (∑ k : Fin (n - 1), (Bdata.G i k : Int)) =
          (Brow i : Int) := by
      exact_mod_cast Bdata.G_row_sum i
    have hsumB3 :
        (∑ k : Fin (n - 1), 3 * (Bdata.G i k : Int)) =
          3 * (Brow i : Int) := by
      rw [← Finset.mul_sum, hsumB]
    have hsum :
        (∑ k : Fin (n - 1),
          qge2LayeredSignedEntry (Adata.G i k) (Bdata.G i k))
          =
        (∑ k : Fin (n - 1),
          ((Adata.G i k : Int) + 3 * (Bdata.G i k : Int)))
          - 2 * ((n - 1 : Nat) : Int) := by
      simp [qge2LayeredSignedEntry, Finset.sum_add_distrib,
        Finset.sum_const, Fintype.card_fin, mul_comm]
      ring
    rw [hsum]
    calc
      (∑ k : Fin (n - 1), ((Adata.G i k : Int) + 3 * (Bdata.G i k : Int)))
          - 2 * ((n - 1 : Nat) : Int)
          = ((Arow i : Int) + 3 * (Brow i : Int))
              - 2 * ((n - 1 : Nat) : Int) := by
            rw [Finset.sum_add_distrib, hsumA, hsumB3]
      _ = qge2OrdinaryRowTarget n r a epsBit i := by
            rw [hRow i]
            ring

theorem exists_qge2SignedFullSupportTrellisWitness_of_eight_le {n r : Nat}
    (hnEven : Even n) (hn8 : 8 ≤ n) (hrOdd : Odd r)
    (hrlt : r < n) (hrpos : 0 < r)
    (a epsBit : Fin n → Nat) (c : Fin (n - 1) → Nat)
    (ha : ∀ i, a i = 1 ∨ a i = 2)
    (heps : ∀ i, epsBit i = 0 ∨ epsBit i = 1)
    (hc : ∀ k, c k = 1 ∨ c k = 2)
    (heps_sum : (∑ i : Fin n, epsBit i) = r)
    (ha_eq_c : (∑ i : Fin n, a i) = (∑ k : Fin (n - 1), c k)) :
    ∃ X : Fin (n - 1) → Fin n → Int,
      (∀ k i, IsSignedVal (X k i)) ∧
      (∀ k : Fin (n - 1), (∑ i : Fin n, X k i) = - (c k : Int)) ∧
      (∀ i : Fin n,
        (∑ k : Fin (n - 1), X k i) =
          qge2OrdinaryRowTarget n r a epsBit i) :=
  exists_qge2SignedFullSupportTrellisWitness_of_binaryLayerDegreeData
    (exists_qge2BinaryLayerDegreeData_of_eight_le
      hnEven hn8 hrOdd hrlt hrpos a epsBit c
      ha heps hc heps_sum ha_eq_c)

def OrdinaryQge2SmallSignedFullSupportTrellisGoal : Prop :=
  ∀ {n r : Nat},
    Even n → 4 ≤ n → n < 10 → Odd r → r < n → 0 < r →
    ∀ (a : Fin n → Nat) (epsBit : Fin n → Nat) (c : Fin (n - 1) → Nat),
      (∀ i : Fin n, a i = 1 ∨ a i = 2) →
      (∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1) →
      (∀ k : Fin (n - 1), c k = 1 ∨ c k = 2) →
      (∑ i : Fin n, epsBit i) = r →
      (∑ i : Fin n, a i) = (∑ k : Fin (n - 1), c k) →
      (∀ w : Fin n → Int,
        (∑ i : Fin n, w i * qge2OrdinaryRowTarget n r a epsBit i)
          ≤ ∑ k : Fin (n - 1), qge2SignedColumnSupport n (c k) w) →
      ∃ X : Fin (n - 1) → Fin n → Int,
        (∀ k i, IsSignedVal (X k i)) ∧
        (∀ k : Fin (n - 1), (∑ i : Fin n, X k i) = - (c k : Int)) ∧
        (∀ i : Fin n,
        (∑ k : Fin (n - 1), X k i) =
          qge2OrdinaryRowTarget n r a epsBit i)

def OrdinaryQge2SignedFullSupportTrellisGoalAt (n0 : Nat) : Prop :=
  ∀ {n r : Nat}, n = n0 →
    Even n → 4 ≤ n → Odd r → r < n → 0 < r →
    ∀ (a : Fin n → Nat) (epsBit : Fin n → Nat) (c : Fin (n - 1) → Nat),
      (∀ i : Fin n, a i = 1 ∨ a i = 2) →
      (∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1) →
      (∀ k : Fin (n - 1), c k = 1 ∨ c k = 2) →
      (∑ i : Fin n, epsBit i) = r →
      (∑ i : Fin n, a i) = (∑ k : Fin (n - 1), c k) →
      (∀ w : Fin n → Int,
        (∑ i : Fin n, w i * qge2OrdinaryRowTarget n r a epsBit i)
          ≤ ∑ k : Fin (n - 1), qge2SignedColumnSupport n (c k) w) →
      ∃ X : Fin (n - 1) → Fin n → Int,
        (∀ k i, IsSignedVal (X k i)) ∧
        (∀ k : Fin (n - 1), (∑ i : Fin n, X k i) = - (c k : Int)) ∧
        (∀ i : Fin n,
          (∑ k : Fin (n - 1), X k i) =
            qge2OrdinaryRowTarget n r a epsBit i)

theorem ordinaryQge2SmallSignedFullSupportTrellisGoal_of_at_four_six_eight
    (h4 : OrdinaryQge2SignedFullSupportTrellisGoalAt 4)
    (h6 : OrdinaryQge2SignedFullSupportTrellisGoalAt 6)
    (h8 : OrdinaryQge2SignedFullSupportTrellisGoalAt 8) :
    OrdinaryQge2SmallSignedFullSupportTrellisGoal := by
  intro n r hnEven hn4 hnlt10 hrOdd hrlt hrpos
    a epsBit c ha heps hc heps_sum ha_eq_c hSupport
  have hn : n = 4 ∨ n = 6 ∨ n = 8 := by
    rcases hnEven with ⟨m, hm⟩
    omega
  rcases hn with hn | hn | hn
  · exact h4 hn hnEven hn4 hrOdd hrlt hrpos
      a epsBit c ha heps hc heps_sum ha_eq_c hSupport
  · exact h6 hn hnEven hn4 hrOdd hrlt hrpos
      a epsBit c ha heps hc heps_sum ha_eq_c hSupport
  · exact h8 hn hnEven hn4 hrOdd hrlt hrpos
      a epsBit c ha heps hc heps_sum ha_eq_c hSupport

theorem ordinaryQge2SignedFullSupportTrellisGoal_of_smallGoal
    (hSmall : OrdinaryQge2SmallSignedFullSupportTrellisGoal) :
    OrdinaryQge2SignedFullSupportTrellisGoal := by
  intro n r hnEven hn4 hrOdd hrlt hrpos a epsBit c
    ha heps hc heps_sum ha_eq_c hSupport
  by_cases hn8 : 8 ≤ n
  · exact exists_qge2SignedFullSupportTrellisWitness_of_eight_le
      hnEven hn8 hrOdd hrlt hrpos a epsBit c ha heps hc heps_sum ha_eq_c
  · exact hSmall hnEven hn4 (by omega) hrOdd hrlt hrpos
      a epsBit c ha heps hc heps_sum ha_eq_c hSupport

theorem ordinaryQge2SignedSeedProperCutClosureGoal_of_smallFullSupportGoal
    (hSmall : OrdinaryQge2SmallSignedFullSupportTrellisGoal) :
    OrdinaryQge2SignedSeedProperCutClosureGoal :=
  ordinaryQge2SignedSeedProperCutClosureGoal_of_fullSupportTrellisGoal
    (ordinaryQge2SignedFullSupportTrellisGoal_of_smallGoal hSmall)

theorem ordinaryQge2SignedFullSupportTrellisGoal_of_at_four_six_eight
    (h4 : OrdinaryQge2SignedFullSupportTrellisGoalAt 4)
    (h6 : OrdinaryQge2SignedFullSupportTrellisGoalAt 6)
    (h8 : OrdinaryQge2SignedFullSupportTrellisGoalAt 8) :
    OrdinaryQge2SignedFullSupportTrellisGoal :=
  ordinaryQge2SignedFullSupportTrellisGoal_of_smallGoal
    (ordinaryQge2SmallSignedFullSupportTrellisGoal_of_at_four_six_eight
      h4 h6 h8)

theorem ordinaryQge2SignedSeedProperCutClosureGoal_of_at_four_six_eight
    (h4 : OrdinaryQge2SignedFullSupportTrellisGoalAt 4)
    (h6 : OrdinaryQge2SignedFullSupportTrellisGoalAt 6)
    (h8 : OrdinaryQge2SignedFullSupportTrellisGoalAt 8) :
    OrdinaryQge2SignedSeedProperCutClosureGoal :=
  ordinaryQge2SignedSeedProperCutClosureGoal_of_fullSupportTrellisGoal
    (ordinaryQge2SignedFullSupportTrellisGoal_of_at_four_six_eight
      h4 h6 h8)

theorem ordinaryQge2SignedFullSupportTrellisGoalAt_eight :
    OrdinaryQge2SignedFullSupportTrellisGoalAt 8 := by
  intro n r hn hnEven _hn4 hrOdd hrlt hrpos a epsBit c
    ha heps hc heps_sum ha_eq_c _hSupport
  subst n
  exact exists_qge2SignedFullSupportTrellisWitness_of_eight_le
    hnEven (by omega) hrOdd hrlt hrpos a epsBit c
    ha heps hc heps_sum ha_eq_c

theorem ordinaryQge2SignedFullSupportTrellisGoalAt_six :
    OrdinaryQge2SignedFullSupportTrellisGoalAt 6 := by
  intro n r hn _hnEven _hn4 hrOdd hrlt hrpos a epsBit c
    ha heps hc heps_sum ha_eq_c _hSupport
  subst n
  exact exists_qge2SignedFullSupportTrellisWitness_of_binaryLayerDegreeData
    (exists_qge2C2LowBinaryLayerDegreeData_of_three_half
      hrOdd hrlt hrpos a epsBit c ha heps hc heps_sum ha_eq_c)

theorem exists_qge2SignedWitness_of_six {r : Nat}
    (hrOdd : Odd r) (hrlt : r < 3 + 3) (hrpos : 0 < r)
    (a epsBit : Fin (3 + 3) → Nat)
    (c : Fin ((3 + 3) - 1) → Nat)
    (ha : ∀ i, a i = 1 ∨ a i = 2)
    (heps : ∀ i, epsBit i = 0 ∨ epsBit i = 1)
    (hc : ∀ k, c k = 1 ∨ c k = 2)
    (heps_sum : (∑ i : Fin (3 + 3), epsBit i) = r)
    (ha_eq_c :
      (∑ i : Fin (3 + 3), a i) =
        (∑ k : Fin ((3 + 3) - 1), c k)) :
    ∃ X : Fin ((3 + 3) - 1) → Fin (3 + 3) → Int,
      (∀ k i, IsSignedVal (X k i)) ∧
      (∀ k : Fin ((3 + 3) - 1), (∑ i : Fin (3 + 3), X k i) =
        - (c k : Int)) ∧
      (∀ i : Fin (3 + 3), (∑ k : Fin ((3 + 3) - 1), X k i) =
        qge2OrdinaryRowTarget (3 + 3) r a epsBit i) :=
  exists_qge2SignedFullSupportTrellisWitness_of_binaryLayerDegreeData
    (exists_qge2C2LowBinaryLayerDegreeData_of_three_half
      hrOdd hrlt hrpos a epsBit c ha heps hc heps_sum ha_eq_c)

theorem exists_qge2SignedWitness_of_four {r : Nat}
    (hrOdd : Odd r) (hrlt : r < 2 + 2)
    (a epsBit : Fin (2 + 2) → Nat)
    (c : Fin ((2 + 2) - 1) → Nat)
    (ha : ∀ i, a i = 1 ∨ a i = 2)
    (heps : ∀ i, epsBit i = 0 ∨ epsBit i = 1)
    (hc : ∀ k, c k = 1 ∨ c k = 2)
    (heps_sum : (∑ i : Fin (2 + 2), epsBit i) = r)
    (ha_eq_c :
      (∑ i : Fin (2 + 2), a i) =
        (∑ k : Fin ((2 + 2) - 1), c k)) :
    ∃ X : Fin ((2 + 2) - 1) → Fin (2 + 2) → Int,
      (∀ k i, IsSignedVal (X k i)) ∧
      (∀ k : Fin ((2 + 2) - 1), (∑ i : Fin (2 + 2), X k i) =
        - (c k : Int)) ∧
      (∀ i : Fin (2 + 2), (∑ k : Fin ((2 + 2) - 1), X k i) =
        qge2OrdinaryRowTarget (2 + 2) r a epsBit i) := by
  let a2 : Fin (2 + 2) → Bool := fun i => decide (a i = 2)
  let eps1 : Fin (2 + 2) → Bool := fun i => decide (epsBit i = 1)
  let c2 : Fin ((2 + 2) - 1) → Bool := fun k => decide (c k = 2)
  have hFor :
      ∀ rf : Fin 2, qge2FourOdd rf = r →
        ∃ X : Fin ((2 + 2) - 1) → Fin (2 + 2) → Int,
          (∀ k i, IsSignedVal (X k i)) ∧
          (∀ k : Fin ((2 + 2) - 1), (∑ i : Fin (2 + 2), X k i) =
            - (c k : Int)) ∧
          (∀ i : Fin (2 + 2), (∑ k : Fin ((2 + 2) - 1), X k i) =
            qge2OrdinaryRowTarget (2 + 2) r a epsBit i) := by
    intro rf hrf
    have hEpsTable :
        (∑ i : Fin (2 + 2), qge2SixEpsVal (eps1 i)) =
          qge2FourOdd rf := by
      rw [hrf]
      calc
        (∑ i : Fin (2 + 2), qge2SixEpsVal (eps1 i))
            = ∑ i : Fin (2 + 2), epsBit i := by
              apply Finset.sum_congr rfl
              intro i _
              dsimp [eps1]
              exact qge2SixEpsVal_decide_eq (heps i)
        _ = r := heps_sum
    have hAeqTable :
        (∑ i : Fin (2 + 2), qge2SixAVal (a2 i)) =
          (∑ k : Fin ((2 + 2) - 1), qge2SixAVal (c2 k)) := by
      calc
        (∑ i : Fin (2 + 2), qge2SixAVal (a2 i))
            = ∑ i : Fin (2 + 2), a i := by
              apply Finset.sum_congr rfl
              intro i _
              dsimp [a2]
              exact qge2SixAVal_decide_eq (ha i)
        _ = ∑ k : Fin ((2 + 2) - 1), c k := ha_eq_c
        _ = ∑ k : Fin ((2 + 2) - 1), qge2SixAVal (c2 k) := by
              apply Finset.sum_congr rfl
              intro k _
              dsimp [c2]
              exact (qge2SixAVal_decide_eq (hc k)).symm
    rcases qge2FourColumnCodeTable rf a2 eps1 c2 hEpsTable hAeqTable with
      ⟨code, _hvalid, hSigned, hCol, hRow⟩
    refine ⟨fun k i => qge2FourColumnVal (c2 k) (code k) i,
      hSigned, ?_, ?_⟩
    · intro k
      have hck : qge2SixAVal (c2 k) = c k := by
        dsimp [c2]
        exact qge2SixAVal_decide_eq (hc k)
      rw [hCol k, hck]
    · intro i
      have hodd : 2 * rf.val + 1 = r := by
        simpa [qge2FourOdd] using hrf
      rw [hRow i]
      rcases ha i with hai | hai <;> rcases heps i with hei | hei <;>
        simp [qge2FourOrdRowTarget, qge2FourOdd, qge2SixAVal,
          qge2SixEpsVal, qge2OrdinaryRowTarget, a2, eps1, hodd, hai, hei]
  have hrCases : r = 1 ∨ r = 3 := by
    rcases hrOdd with ⟨s, hs⟩
    omega
  rcases hrCases with rfl | rfl
  · exact hFor ⟨0, by decide⟩ rfl
  · exact hFor ⟨1, by decide⟩ rfl

theorem ordinaryQge2SignedFullSupportTrellisGoalAt_four :
    OrdinaryQge2SignedFullSupportTrellisGoalAt 4 := by
  intro n r hn _hnEven _hn4 hrOdd hrlt hrpos a epsBit c
    ha heps hc heps_sum ha_eq_c _hSupport
  subst n
  exact exists_qge2SignedWitness_of_four
    hrOdd hrlt a epsBit c ha heps hc heps_sum ha_eq_c

/--
Manuscript-facing ordinary q>=2 signed binary-layer closure.

This is the direct Appendix-A style statement: for ordinary q>=2 row data, the
signed matrix exists without assuming full-support inequalities.  The proof
uses the binary-layer construction in large dimensions and the explicit
`n = 4, 6` closures in the small even cases.
-/
def OrdinaryQge2SignedBinaryLayerClosureGoal : Prop :=
  ∀ {n r : Nat},
    Even n → 4 ≤ n → Odd r → r < n → 0 < r →
    ∀ (a : Fin n → Nat) (epsBit : Fin n → Nat) (c : Fin (n - 1) → Nat),
      (∀ i : Fin n, a i = 1 ∨ a i = 2) →
      (∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1) →
      (∀ k : Fin (n - 1), c k = 1 ∨ c k = 2) →
      (∑ i : Fin n, epsBit i) = r →
      (∑ i : Fin n, a i) = (∑ k : Fin (n - 1), c k) →
      ∃ X : Fin (n - 1) → Fin n → Int,
        (∀ k i, IsSignedVal (X k i)) ∧
        (∀ k : Fin (n - 1), (∑ i : Fin n, X k i) = - (c k : Int)) ∧
        (∀ i : Fin n,
          (∑ k : Fin (n - 1), X k i) =
            qge2OrdinaryRowTarget n r a epsBit i)

theorem ordinaryQge2SignedBinaryLayerClosureGoal :
    OrdinaryQge2SignedBinaryLayerClosureGoal := by
  intro n r hnEven hn4 hrOdd hrlt hrpos a epsBit c
    ha heps hc heps_sum ha_eq_c
  by_cases hn8 : 8 ≤ n
  · exact exists_qge2SignedFullSupportTrellisWitness_of_eight_le
      hnEven hn8 hrOdd hrlt hrpos a epsBit c ha heps hc heps_sum ha_eq_c
  · have hnSmall : n = 4 ∨ n = 6 := by
      rcases hnEven with ⟨m, hm⟩
      omega
    rcases hnSmall with rfl | rfl
    · exact exists_qge2SignedWitness_of_four
        hrOdd hrlt a epsBit c ha heps hc heps_sum ha_eq_c
    · exact exists_qge2SignedWitness_of_six
        hrOdd hrlt hrpos a epsBit c ha heps hc heps_sum ha_eq_c

theorem ordinaryQge2SignedFullSupportTrellisGoal_of_binaryLayerClosureGoal
    (hClosure : OrdinaryQge2SignedBinaryLayerClosureGoal) :
    OrdinaryQge2SignedFullSupportTrellisGoal := by
  intro n r hnEven hn4 hrOdd hrlt hrpos a epsBit c
    ha heps hc heps_sum ha_eq_c _hSupport
  exact hClosure hnEven hn4 hrOdd hrlt hrpos
    a epsBit c ha heps hc heps_sum ha_eq_c

theorem ordinaryQge2SignedFullSupportTrellisGoal_of_at_four_six
    (h4 : OrdinaryQge2SignedFullSupportTrellisGoalAt 4)
    (h6 : OrdinaryQge2SignedFullSupportTrellisGoalAt 6) :
    OrdinaryQge2SignedFullSupportTrellisGoal :=
  ordinaryQge2SignedFullSupportTrellisGoal_of_at_four_six_eight
    h4 h6 ordinaryQge2SignedFullSupportTrellisGoalAt_eight

theorem ordinaryQge2SignedFullSupportTrellisGoal :
    OrdinaryQge2SignedFullSupportTrellisGoal :=
  ordinaryQge2SignedFullSupportTrellisGoal_of_binaryLayerClosureGoal
    ordinaryQge2SignedBinaryLayerClosureGoal

theorem ordinaryQge2SignedSeedProperCutClosureGoal_of_at_four_six
    (h4 : OrdinaryQge2SignedFullSupportTrellisGoalAt 4)
    (h6 : OrdinaryQge2SignedFullSupportTrellisGoalAt 6) :
    OrdinaryQge2SignedSeedProperCutClosureGoal :=
  ordinaryQge2SignedSeedProperCutClosureGoal_of_fullSupportTrellisGoal
    (ordinaryQge2SignedFullSupportTrellisGoal_of_at_four_six h4 h6)

theorem ordinaryQge2SignedSeedProperCutClosureGoal :
    OrdinaryQge2SignedSeedProperCutClosureGoal :=
  ordinaryQge2SignedSeedProperCutClosureGoal_of_fullSupportTrellisGoal
    ordinaryQge2SignedFullSupportTrellisGoal

theorem ordinaryQge2BinaryLayerTrellisGoal_of_degreeGoal
    (hDegree : OrdinaryQge2BinaryLayerDegreeGoal) :
    OrdinaryQge2BinaryLayerTrellisGoal := by
  classical
  intro n r hnEven hn4 hrOdd hrlt hrpos a epsBit c
    ha heps hc heps_sum ha_eq_c hSupport
  rcases hDegree hnEven hn4 hrOdd hrlt hrpos a epsBit c
      ha heps hc heps_sum ha_eq_c hSupport with
    ⟨Arow, Brow, Acol, Bcol, hAdata, hBdata, hCol, hRow⟩
  rcases hAdata with ⟨Adata⟩
  rcases hBdata with ⟨Bdata⟩
  refine ⟨Adata.G, Bdata.G, Adata.G_zero_one, Bdata.G_zero_one, ?_, ?_⟩
  · intro k
    have hsumA :
        (∑ i : Fin n, (Adata.G i k : Int)) = (Acol k : Int) := by
      exact_mod_cast Adata.G_col_sum k
    have hsumB :
        (∑ i : Fin n, (Bdata.G i k : Int)) = (Bcol k : Int) := by
      exact_mod_cast Bdata.G_col_sum k
    calc
      (∑ i : Fin n,
          ((Adata.G i k : Int) + 3 * (Bdata.G i k : Int)))
          = (∑ i : Fin n, (Adata.G i k : Int)) +
              3 * (∑ i : Fin n, (Bdata.G i k : Int)) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ = (Acol k : Int) + 3 * (Bcol k : Int) := by
            rw [hsumA, hsumB]
      _ = 2 * (n : Int) - (c k : Int) := hCol k
  · intro i
    have hsumA :
        (∑ k : Fin (n - 1), (Adata.G i k : Int)) =
          (Arow i : Int) := by
      exact_mod_cast Adata.G_row_sum i
    have hsumB :
        (∑ k : Fin (n - 1), (Bdata.G i k : Int)) =
          (Brow i : Int) := by
      exact_mod_cast Bdata.G_row_sum i
    calc
      (∑ k : Fin (n - 1),
          ((Adata.G i k : Int) + 3 * (Bdata.G i k : Int)))
          = (∑ k : Fin (n - 1), (Adata.G i k : Int)) +
              3 * (∑ k : Fin (n - 1), (Bdata.G i k : Int)) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ = (Arow i : Int) + 3 * (Brow i : Int) := by
            rw [hsumA, hsumB]
      _ = qge2OrdinaryRowTarget n r a epsBit i +
              2 * ((n - 1 : Nat) : Int) := hRow i

theorem ordinaryQge2SignedFullSupportTrellisGoal_of_binaryLayerTrellisGoal
    (hLayer : OrdinaryQge2BinaryLayerTrellisGoal) :
    OrdinaryQge2SignedFullSupportTrellisGoal := by
  classical
  intro n r hnEven hn4 hrOdd hrlt hrpos a epsBit c
    ha heps hc heps_sum ha_eq_c hSupport
  rcases hLayer hnEven hn4 hrOdd hrlt hrpos a epsBit c
      ha heps hc heps_sum ha_eq_c hSupport with
    ⟨A, B, hA01, hB01, hCol, hRow⟩
  refine ⟨fun k i => qge2LayeredSignedEntry (A i k) (B i k), ?_, ?_, ?_⟩
  · intro k i
    exact qge2LayeredSignedEntry_isSigned (hA01 i k) (hB01 i k)
  · intro k
    have hsum :
        (∑ i : Fin n, qge2LayeredSignedEntry (A i k) (B i k))
          =
        (∑ i : Fin n, ((A i k : Int) + 3 * (B i k : Int)))
          - 2 * (n : Int) := by
      simp [qge2LayeredSignedEntry, Finset.sum_add_distrib,
        Finset.sum_const, Fintype.card_fin, mul_comm]
      ring
    rw [hsum, hCol k]
    ring
  · intro i
    have hsum :
        (∑ k : Fin (n - 1), qge2LayeredSignedEntry (A i k) (B i k))
          =
        (∑ k : Fin (n - 1), ((A i k : Int) + 3 * (B i k : Int)))
          - 2 * ((n - 1 : Nat) : Int) := by
      simp [qge2LayeredSignedEntry, Finset.sum_add_distrib,
        Finset.sum_const, Fintype.card_fin, mul_comm]
      ring
    rw [hsum, hRow i]
    ring

theorem ordinaryQge2SignedFullSupportTrellisGoal_of_binaryLayerDegreeGoal
    (hDegree : OrdinaryQge2BinaryLayerDegreeGoal) :
    OrdinaryQge2SignedFullSupportTrellisGoal :=
  ordinaryQge2SignedFullSupportTrellisGoal_of_binaryLayerTrellisGoal
    (ordinaryQge2BinaryLayerTrellisGoal_of_degreeGoal hDegree)

theorem ordinaryQge2SignedSeedProperCutClosureGoal_of_binaryLayerTrellisGoal
    (hLayer : OrdinaryQge2BinaryLayerTrellisGoal) :
    OrdinaryQge2SignedSeedProperCutClosureGoal :=
  ordinaryQge2SignedSeedProperCutClosureGoal_of_fullSupportTrellisGoal
    (ordinaryQge2SignedFullSupportTrellisGoal_of_binaryLayerTrellisGoal
      hLayer)

theorem ordinaryQge2SignedSeedProperCutClosureGoal_of_binaryLayerDegreeGoal
    (hDegree : OrdinaryQge2BinaryLayerDegreeGoal) :
    OrdinaryQge2SignedSeedProperCutClosureGoal :=
  ordinaryQge2SignedSeedProperCutClosureGoal_of_binaryLayerTrellisGoal
    (ordinaryQge2BinaryLayerTrellisGoal_of_degreeGoal hDegree)

/--
Worker-2 API boundary for the ordinary `q >= 2` signed trellis.

The level-set and half-slack work is closed internally; this theorem exposes it
from the finite-Hoffman namespace boundary so the remaining integrality theorem
can target only `OrdinaryQge2SignedSeedProperCutClosureGoal` or the equivalent
full-support trellis statement.
-/
theorem ordinaryQge2IndicatorToFullSupportGoal :
    OrdinaryQge2IndicatorToFullSupportGoal :=
  ordinaryQge2IndicatorToFullSupportGoal_of_internalHalfSlack

/--
The remaining signed-trellis integrality target can be proved either as the
proper-cut seed closure or as the full-support trellis theorem.
-/
theorem ordinaryQge2SignedSeedProperCutClosureGoal_iff_fullSupportTrellisGoal :
    OrdinaryQge2SignedSeedProperCutClosureGoal ↔
      OrdinaryQge2SignedFullSupportTrellisGoal :=
  ordinaryQge2SignedFullSupportTrellisGoal_iff_seedProperCutClosureGoal.symm

theorem ordinaryQge2SignedTrellisHoffmanGoal_iff_fullSupportTrellisGoal :
    OrdinaryQge2SignedTrellisHoffmanGoal ↔
      OrdinaryQge2SignedFullSupportTrellisGoal :=
  ⟨fun hTrellis =>
      ordinaryQge2SignedFullSupportTrellisGoal_of_seedClosure
        (ordinaryQge2SignedSeedClosureGoal_of_signedTrellisHoffman hTrellis),
    fun hFull =>
      ordinaryQge2SignedTrellisHoffmanGoal_of_fullSupport hFull
        ordinaryQge2IndicatorToFullSupportGoal⟩

end PrefixCount
end RoundComposite
