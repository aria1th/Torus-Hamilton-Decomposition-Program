import Mathlib

namespace RoundComposite
namespace PrefixCount

open scoped BigOperators

/-- Integer primitiveity condition used by signed prefix-count differences. -/
def IntCoprime (a : Int) (m : Nat) : Prop :=
  Nat.Coprime a.natAbs m

/-- Counts for symbols `0`, `Delta`, and the numeric prefix symbols. -/
structure Parts (d : Nat) where
  zero : Fin d → Nat
  delta : Fin d → Nat
  step : Fin d → Fin (d - 2) → Nat

namespace Parts

/--
Prefix-count admissibility, stated before any conversion to a dense
`Fin d × Fin d` matrix.  The primitive conditions are exactly the row
conditions consumed by the prefix-count return lemma.
-/
structure Admissible {d : Nat} (m : Nat) (C : Parts d) : Prop where
  row_sum :
    ∀ i : Fin d,
      C.zero i + C.delta i + (∑ k : Fin (d - 2), C.step i k) = m
  col_zero :
    (∑ i : Fin d, C.zero i) = m
  col_delta :
    (∑ i : Fin d, C.delta i) = m
  col_step :
    ∀ k : Fin (d - 2), (∑ i : Fin d, C.step i k) = m
  prim_zero :
    ∀ i : Fin d, Nat.Coprime (C.zero i) m
  prim_step :
    ∀ i : Fin d, ∀ k : Fin (d - 2),
      IntCoprime ((C.step i k : Int) - (C.delta i : Int)) m

end Parts

namespace Parts

def colZero {d : Nat} (hd : 2 ≤ d) : Fin d :=
  ⟨0, by omega⟩

def colDelta {d : Nat} (hd : 2 ≤ d) : Fin d :=
  ⟨1, by omega⟩

def colStep {d : Nat} (hd : 2 ≤ d) (k : Fin (d - 2)) : Fin d :=
  ⟨k.val + 2, by omega⟩

def stepIndexOfColumn {d : Nat} (hd : 2 ≤ d)
    (j : Fin d) (hj0 : j.val ≠ 0) (hj1 : j.val ≠ 1) : Fin (d - 2) :=
  ⟨j.val - 2, by omega⟩

def toMatrix {d : Nat} (hd : 2 ≤ d) (C : Parts d) :
    Matrix (Fin d) (Fin d) Nat :=
  fun i j =>
    if hj0 : j.val = 0 then
      C.zero i
    else if hj1 : j.val = 1 then
      C.delta i
    else
      C.step i (stepIndexOfColumn hd j hj0 hj1)

@[simp] theorem toMatrix_colZero {d : Nat} (hd : 2 ≤ d)
    (C : Parts d) (i : Fin d) :
    C.toMatrix hd i (colZero hd) = C.zero i := by
  simp [toMatrix, colZero]

@[simp] theorem toMatrix_colDelta {d : Nat} (hd : 2 ≤ d)
    (C : Parts d) (i : Fin d) :
    C.toMatrix hd i (colDelta hd) = C.delta i := by
  simp [toMatrix, colDelta]

@[simp] theorem toMatrix_colStep {d : Nat} (hd : 2 ≤ d)
    (C : Parts d) (i : Fin d) (k : Fin (d - 2)) :
    C.toMatrix hd i (colStep hd k) = C.step i k := by
  simp [toMatrix, colStep, stepIndexOfColumn]

def colsEquiv {d : Nat} (hd : 2 ≤ d) : Fin d ≃ Fin 2 ⊕ Fin (d - 2) :=
  (finCongr (by omega : d = 2 + (d - 2))).trans finSumFinEquiv.symm

@[simp] theorem colsEquiv_symm_inl_zero {d : Nat} (hd : 2 ≤ d) :
    (colsEquiv hd).symm (Sum.inl (0 : Fin 2)) = colZero hd := by
  ext
  simp [colsEquiv, colZero]

@[simp] theorem colsEquiv_symm_inl_one {d : Nat} (hd : 2 ≤ d) :
    (colsEquiv hd).symm (Sum.inl (1 : Fin 2)) = colDelta hd := by
  ext
  simp [colsEquiv, colDelta]

@[simp] theorem colsEquiv_symm_inr {d : Nat} (hd : 2 ≤ d)
    (k : Fin (d - 2)) :
    (colsEquiv hd).symm (Sum.inr k) = colStep hd k := by
  ext
  simp [colsEquiv, colStep, finSumFinEquiv_apply_right]
  omega

theorem sum_cols_split {d : Nat} (hd : 2 ≤ d)
    {α : Type*} [AddCommMonoid α] (f : Fin d → α) :
    (∑ j : Fin d, f j)
      = f (colZero hd) + f (colDelta hd)
          + ∑ k : Fin (d - 2), f (colStep hd k) := by
  trans ∑ x : Fin 2 ⊕ Fin (d - 2), f ((colsEquiv hd).symm x)
  · exact Fintype.sum_equiv (colsEquiv hd) f
      (fun x => f ((colsEquiv hd).symm x)) (by intro x; simp)
  rw [Fintype.sum_sum_type]
  rw [Fin.sum_univ_two]
  simp [add_assoc]

end Parts

/-- Dense matrix version of prefix-count admissibility. -/
structure MatrixAdmissible {d : Nat} (hd : 2 ≤ d) (m : Nat)
    (M : Matrix (Fin d) (Fin d) Nat) : Prop where
  row_sum : ∀ i : Fin d, (∑ j : Fin d, M i j) = m
  col_sum : ∀ j : Fin d, (∑ i : Fin d, M i j) = m
  prim_zero : ∀ i : Fin d, Nat.Coprime (M i (Parts.colZero hd)) m
  prim_step : ∀ i : Fin d, ∀ k : Fin (d - 2),
    IntCoprime ((M i (Parts.colStep hd k) : Int)
      - (M i (Parts.colDelta hd) : Int)) m

/-- The row/column regularity needed for permutation-layer realization. -/
structure MatrixBalanced {d : Nat} (m : Nat)
    (M : Matrix (Fin d) (Fin d) Nat) : Prop where
  row_sum : ∀ i : Fin d, (∑ j : Fin d, M i j) = m
  col_sum : ∀ j : Fin d, (∑ i : Fin d, M i j) = m

namespace MatrixAdmissible

theorem toBalanced {d m : Nat} {M : Matrix (Fin d) (Fin d) Nat}
    {hd : 2 ≤ d} (hM : MatrixAdmissible hd m M) :
    MatrixBalanced m M where
  row_sum := hM.row_sum
  col_sum := hM.col_sum

end MatrixAdmissible

/-- A decomposition of a dense count matrix into `m` layer permutations. -/
structure LayerPermCounts (d m : Nat)
    (M : Matrix (Fin d) (Fin d) Nat) where
  layer : Fin m → Equiv.Perm (Fin d)
  count_eq : ∀ i j : Fin d,
    (∑ t : Fin m, if layer t i = j then (1 : Nat) else 0) = M i j

namespace LayerPermCounts

theorem row_sum {d m : Nat} {M : Matrix (Fin d) (Fin d) Nat}
    (L : LayerPermCounts d m M) :
    ∀ i : Fin d, (∑ j : Fin d, M i j) = m := by
  intro i
  calc
    (∑ j : Fin d, M i j)
        = ∑ j : Fin d, ∑ t : Fin m,
            if L.layer t i = j then (1 : Nat) else 0 := by
          simp [← L.count_eq]
    _ = ∑ t : Fin m, ∑ j : Fin d,
            if L.layer t i = j then (1 : Nat) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ _t : Fin m, 1 := by
          simp
    _ = m := by
          simp

theorem col_sum {d m : Nat} {M : Matrix (Fin d) (Fin d) Nat}
    (L : LayerPermCounts d m M) :
    ∀ j : Fin d, (∑ i : Fin d, M i j) = m := by
  intro j
  calc
    (∑ i : Fin d, M i j)
        = ∑ i : Fin d, ∑ t : Fin m,
            if L.layer t i = j then (1 : Nat) else 0 := by
          simp [← L.count_eq]
    _ = ∑ t : Fin m, ∑ i : Fin d,
            if L.layer t i = j then (1 : Nat) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ _t : Fin m, 1 := by
          congr with t
          trans ∑ x : Fin d, if x = j then (1 : Nat) else 0
          · exact Fintype.sum_equiv (L.layer t)
              (fun i => if L.layer t i = j then (1 : Nat) else 0)
              (fun x => if x = j then (1 : Nat) else 0)
              (by intro i; rfl)
          · simp
    _ = m := by
          simp

theorem toMatrixAdmissible {d m : Nat} {M : Matrix (Fin d) (Fin d) Nat}
    (hd : 2 ≤ d) (L : LayerPermCounts d m M)
    (hzero : ∀ i : Fin d, Nat.Coprime (M i (Parts.colZero hd)) m)
    (hstep : ∀ i : Fin d, ∀ k : Fin (d - 2),
      IntCoprime ((M i (Parts.colStep hd k) : Int)
        - (M i (Parts.colDelta hd) : Int)) m) :
    MatrixAdmissible hd m M where
  row_sum := L.row_sum
  col_sum := L.col_sum
  prim_zero := hzero
  prim_step := hstep

end LayerPermCounts

namespace Parts

theorem Admissible.toMatrixAdmissible {d m : Nat} {C : Parts d}
    (hd : 2 ≤ d) (hC : C.Admissible m) :
    MatrixAdmissible hd m (C.toMatrix hd) where
  row_sum := by
    intro i
    rw [sum_cols_split hd (fun j => C.toMatrix hd i j)]
    simpa [add_assoc] using hC.row_sum i
  col_sum := by
    intro j
    by_cases hj0 : j.val = 0
    · have hj : j = colZero hd := by
        ext
        simp [colZero, hj0]
      subst j
      simpa using hC.col_zero
    · by_cases hj1 : j.val = 1
      · have hj : j = colDelta hd := by
          ext
          simp [colDelta, hj1]
        subst j
        simpa using hC.col_delta
      · have hj : j = colStep hd (stepIndexOfColumn hd j hj0 hj1) := by
          ext
          simp [colStep, stepIndexOfColumn]
          omega
        rw [hj]
        simpa using hC.col_step (stepIndexOfColumn hd j hj0 hj1)
  prim_zero := by
    intro i
    simpa using hC.prim_zero i
  prim_step := by
    intro i k
    simpa using hC.prim_step i k

end Parts

def BalancedMatrixLayerRealizationGoal : Prop :=
  ∀ {d m : Nat} (M : Matrix (Fin d) (Fin d) Nat),
    MatrixBalanced m M →
    Nonempty (LayerPermCounts d m M)

theorem balancedMatrixLayerRealization_zero
    {d : Nat} {M : Matrix (Fin d) (Fin d) Nat}
    (hM : MatrixBalanced 0 M) :
    Nonempty (LayerPermCounts d 0 M) := by
  classical
  refine ⟨{
    layer := fun t => nomatch t
    count_eq := ?_
  }⟩
  intro i j
  have hzero : M i j = 0 := by
    have hrow := hM.row_sum i
    have hentries :
        ∀ x ∈ (Finset.univ : Finset (Fin d)), 0 ≤ M i x := by
      intro x hx
      exact Nat.zero_le (M i x)
    exact (Finset.sum_eq_zero_iff_of_nonneg hentries).mp hrow j (by simp)
  simp [hzero]

def positiveCols {d : Nat} (M : Matrix (Fin d) (Fin d) Nat)
    (i : Fin d) : Finset (Fin d) :=
  Finset.univ.filter fun j => 0 < M i j

theorem matrixBalanced_exists_positive_perm
    {d m : Nat} {M : Matrix (Fin d) (Fin d) Nat}
    (hM : MatrixBalanced (m + 1) M) :
    ∃ π : Equiv.Perm (Fin d), ∀ i : Fin d, 0 < M i (π i) := by
  classical
  let n := m + 1
  have hnpos : 0 < n := by omega
  have hHall :
      ∀ S : Finset (Fin d),
        S.card ≤ (S.biUnion (positiveCols M)).card := by
    intro S
    let B := S.biUnion (positiveCols M)
    have hrowRestrict :
        ∀ i ∈ S, (∑ j : Fin d, M i j) = ∑ j ∈ B, M i j := by
      intro i hi
      symm
      apply Finset.sum_subset (by intro x hx; simp)
      intro x _ hxB
      have hxnot : x ∉ positiveCols M i := by
        intro hxpos
        exact hxB (Finset.mem_biUnion.mpr ⟨i, hi, hxpos⟩)
      have hnotpos : ¬ 0 < M i x := by
        simpa [positiveCols] using hxnot
      omega
    have hleft :
        (∑ _i ∈ S, n) = S.card * n := by
      simp [n]
    have hright :
        (∑ _j ∈ B, n) = B.card * n := by
      simp [n]
    have hmul : S.card * n ≤ B.card * n := by
      rw [← hleft, ← hright]
      calc
        (∑ _i ∈ S, n)
            = ∑ i ∈ S, ∑ j : Fin d, M i j := by
                apply Finset.sum_congr rfl
                intro i hi
                simp [n, hM.row_sum i]
        _ = ∑ i ∈ S, ∑ j ∈ B, M i j := by
                apply Finset.sum_congr rfl
                intro i hi
                exact hrowRestrict i hi
        _ = ∑ j ∈ B, ∑ i ∈ S, M i j := by
                rw [Finset.sum_comm]
        _ ≤ ∑ j ∈ B, ∑ i : Fin d, M i j := by
                apply Finset.sum_le_sum
                intro j hj
                exact Finset.sum_le_sum_of_subset
                  (by intro i hi; simp)
        _ = ∑ _j ∈ B, n := by
                apply Finset.sum_congr rfl
                intro j hj
                simp [n, hM.col_sum j]
    exact Nat.le_of_mul_le_mul_right hmul hnpos
  rcases (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (positiveCols M)).mp hHall with
    ⟨f, hfInj, hfMem⟩
  have hfSurj : Function.Surjective f :=
    hfInj.surjective_of_finite (Equiv.refl (Fin d))
  refine ⟨Equiv.ofBijective f ⟨hfInj, hfSurj⟩, ?_⟩
  intro i
  simpa [positiveCols, Equiv.ofBijective] using hfMem i

def peelLayer {d : Nat} (M : Matrix (Fin d) (Fin d) Nat)
    (π : Equiv.Perm (Fin d)) : Matrix (Fin d) (Fin d) Nat :=
  fun i j => if π i = j then M i j - 1 else M i j

theorem peelLayer_entry_add {d : Nat}
    {M : Matrix (Fin d) (Fin d) Nat} {π : Equiv.Perm (Fin d)}
    (hπ : ∀ i : Fin d, 0 < M i (π i)) (i j : Fin d) :
    peelLayer M π i j + (if π i = j then (1 : Nat) else 0) = M i j := by
  by_cases h : π i = j
  · have hpos : 0 < M i j := by
      simpa [h] using hπ i
    simp [peelLayer, h, Nat.sub_add_cancel hpos]
  · simp [peelLayer, h]

theorem peelLayer_balanced
    {d m : Nat} {M : Matrix (Fin d) (Fin d) Nat}
    (hM : MatrixBalanced (m + 1) M)
    {π : Equiv.Perm (Fin d)}
    (hπ : ∀ i : Fin d, 0 < M i (π i)) :
    MatrixBalanced m (peelLayer M π) where
  row_sum := by
    intro i
    have hsum :
        (∑ j : Fin d, M i j)
          = (∑ j : Fin d, peelLayer M π i j) + 1 := by
      calc
        (∑ j : Fin d, M i j)
            = ∑ j : Fin d,
                (peelLayer M π i j
                  + if π i = j then (1 : Nat) else 0) := by
                apply Finset.sum_congr rfl
                intro j hj
                exact (peelLayer_entry_add hπ i j).symm
        _ = (∑ j : Fin d, peelLayer M π i j)
              + ∑ j : Fin d, (if π i = j then (1 : Nat) else 0) := by
                rw [Finset.sum_add_distrib]
        _ = (∑ j : Fin d, peelLayer M π i j) + 1 := by
                simp
    have hrow := hM.row_sum i
    omega
  col_sum := by
    intro j
    have hsum :
        (∑ i : Fin d, M i j)
          = (∑ i : Fin d, peelLayer M π i j) + 1 := by
      calc
        (∑ i : Fin d, M i j)
            = ∑ i : Fin d,
                (peelLayer M π i j
                  + if π i = j then (1 : Nat) else 0) := by
                apply Finset.sum_congr rfl
                intro i hi
                exact (peelLayer_entry_add hπ i j).symm
        _ = (∑ i : Fin d, peelLayer M π i j)
              + ∑ i : Fin d, (if π i = j then (1 : Nat) else 0) := by
                rw [Finset.sum_add_distrib]
        _ = (∑ i : Fin d, peelLayer M π i j) + 1 := by
                congr 1
                trans ∑ x : Fin d, if x = j then (1 : Nat) else 0
                · exact Fintype.sum_equiv π
                    (fun i => if π i = j then (1 : Nat) else 0)
                    (fun x => if x = j then (1 : Nat) else 0)
                    (by intro i; rfl)
                · simp
    have hcol := hM.col_sum j
    omega

theorem balancedMatrixLayerRealizationGoal :
    BalancedMatrixLayerRealizationGoal := by
  intro d m
  induction m with
  | zero =>
      intro M hM
      exact balancedMatrixLayerRealization_zero hM
  | succ m ih =>
      intro M hM
      rcases matrixBalanced_exists_positive_perm hM with ⟨π, hπ⟩
      rcases ih (peelLayer M π) (peelLayer_balanced hM hπ) with ⟨L⟩
      refine ⟨{
        layer := Fin.lastCases π (fun t => L.layer t)
        count_eq := ?_
      }⟩
      intro i j
      rw [Fin.sum_univ_castSucc]
      simp [L.count_eq i j, peelLayer_entry_add hπ i j]

def MatrixLayerRealizationGoal : Prop :=
  ∀ {d m : Nat} (hd : 2 ≤ d) (M : Matrix (Fin d) (Fin d) Nat),
    MatrixAdmissible hd m M →
    Nonempty (LayerPermCounts d m M)

theorem matrixLayerRealizationGoal_of_balanced
    (hBalanced : BalancedMatrixLayerRealizationGoal) :
    MatrixLayerRealizationGoal := by
  intro d m hd M hM
  exact hBalanced M hM.toBalanced

theorem matrixLayerRealizationGoal : MatrixLayerRealizationGoal :=
  matrixLayerRealizationGoal_of_balanced balancedMatrixLayerRealizationGoal

theorem layerRealization_of_matrixLayerRealizationGoal
    (hMatrix : MatrixLayerRealizationGoal)
    {d m : Nat} (hd : 2 ≤ d) (C : Parts d)
    (hC : C.Admissible m) :
    Nonempty (LayerPermCounts d m (C.toMatrix hd)) :=
  hMatrix hd (C.toMatrix hd) (hC.toMatrixAdmissible hd)

/-- The signed differences used by the high-modulus transportation branch. -/
def signedVals : Finset Int :=
  {-2, -1, 1, 2}

def IsSignedVal (a : Int) : Prop :=
  a ∈ signedVals

theorem signedVal_coprime_of_odd
    {a : Int} {m : Nat} (ha : IsSignedVal a) (hm : Odd m) :
    IntCoprime a m := by
  have ha' : a = -2 ∨ a = -1 ∨ a = 1 ∨ a = 2 := by
    simpa [IsSignedVal, signedVals] using ha
  rcases ha' with rfl | rfl | rfl | rfl
  · simpa [IntCoprime] using hm.coprime_two_left
  · simp [IntCoprime]
  · simp [IntCoprime]
  · simpa [IntCoprime] using hm.coprime_two_left

theorem signedVal_ge_neg_two {a : Int} (ha : IsSignedVal a) :
    (-2 : Int) ≤ a := by
  have ha' : a = -2 ∨ a = -1 ∨ a = 1 ∨ a = 2 := by
    simpa [IsSignedVal, signedVals] using ha
  rcases ha' with rfl | rfl | rfl | rfl <;> norm_num

theorem signedVal_le_two {a : Int} (ha : IsSignedVal a) :
    a ≤ (2 : Int) := by
  have ha' : a = -2 ∨ a = -1 ∨ a = 1 ∨ a = 2 := by
    simpa [IsSignedVal, signedVals] using ha
  rcases ha' with rfl | rfl | rfl | rfl <;> norm_num

theorem one_le_div_pred_of_le {d m : Nat} (hd2 : 2 ≤ d) (hmd : d ≤ m) :
    1 ≤ m / (d - 1) := by
  have hden : 0 < d - 1 := by omega
  exact (Nat.le_div_iff_mul_le hden).2 (by omega)

theorem pred_mod_pos_of_odd
    {d m : Nat} (hdodd : Odd d) (hmodd : Odd m) (hd2 : 2 ≤ d) :
    0 < m % (d - 1) := by
  have hden : 0 < d - 1 := by omega
  by_contra hnot
  have hr0 : m % (d - 1) = 0 := by omega
  rcases hdodd with ⟨k, hk⟩
  have hpred : d - 1 = 2 * k := by omega
  have hm_eq : m = (d - 1) * (m / (d - 1)) := by
    have hdiv := Nat.div_add_mod m (d - 1)
    omega
  have hmeven : Even m := by
    refine ⟨k * (m / (d - 1)), ?_⟩
    calc
      m = (d - 1) * (m / (d - 1)) := hm_eq
      _ = (2 * k) * (m / (d - 1)) := by rw [hpred]
      _ = k * (m / (d - 1)) + k * (m / (d - 1)) := by ring
  exact (Nat.not_even_iff_odd.mpr hmodd) hmeven

theorem pred_mul_div_add_mod (d m : Nat) :
    (d - 1) * (m / (d - 1)) + m % (d - 1) = m := by
  exact Nat.div_add_mod m (d - 1)

theorem quotient_one_or_ge_two_of_le
    {d m : Nat} (hd2 : 2 ≤ d) (hmd : d ≤ m) :
    m / (d - 1) = 1 ∨ 2 ≤ m / (d - 1) := by
  have hq : 1 ≤ m / (d - 1) := one_le_div_pred_of_le hd2 hmd
  omega

theorem quotient_remainder_count_branch
    {d m : Nat} (hdodd : Odd d) (hmodd : Odd m)
    (hd2 : 2 ≤ d) (hmd : d ≤ m) :
    m = (d - 1) * (m / (d - 1)) + m % (d - 1) ∧
    m % (d - 1) < d - 1 ∧
    0 < m % (d - 1) ∧
    (m / (d - 1) = 1 ∨ 2 ≤ m / (d - 1)) := by
  have hden : 0 < d - 1 := by omega
  exact ⟨
    (pred_mul_div_add_mod d m).symm,
    Nat.mod_lt m hden,
    pred_mod_pos_of_odd hdodd hmodd hd2,
    quotient_one_or_ge_two_of_le hd2 hmd
  ⟩

theorem exists_power_two_ge_self_lt_two_mul {L : Nat} (hL : 1 ≤ L) :
    ∃ e : Nat, L ≤ 2 ^ e ∧ 2 ^ e < 2 * L := by
  refine ⟨Nat.clog 2 L, Nat.le_pow_clog (by decide : 1 < 2) L, ?_⟩
  by_cases hL1 : L = 1
  · subst L
    norm_num
  · have hLgt : 1 < L := by omega
    have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hLgt
    have hpos : 0 < Nat.clog 2 L := Nat.clog_pos (by decide : 1 < 2) hLgt
    have hpow : 2 ^ Nat.clog 2 L = 2 * 2 ^ (Nat.clog 2 L).pred := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hpos]
      rw [pow_succ]
      ring
    rw [hpow]
    exact Nat.mul_lt_mul_of_pos_left hpred (by decide)

def oneTwoList (L C : Nat) : List Nat :=
  List.replicate (2 * L - C) 1 ++ List.replicate (C - L) 2

theorem oneTwoList_spec {L C : Nat} (hLC : L ≤ C) (hC2 : C ≤ 2 * L) :
    (oneTwoList L C).length = L ∧
    (oneTwoList L C).sum = C ∧
    ∀ a, a ∈ oneTwoList L C → a = 1 ∨ a = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [oneTwoList]
    omega
  · simp [oneTwoList, List.sum_replicate]
    omega
  · intro a ha
    rw [oneTwoList, List.mem_append] at ha
    simp only [List.mem_replicate] at ha
    rcases ha with ha | ha
    · exact Or.inl ha.2
    · exact Or.inr ha.2

theorem eq_pred_add_mod_of_div_eq_one
    {d m : Nat} (hq : m / (d - 1) = 1) :
    m = (d - 1) + m % (d - 1) := by
  have h := (Nat.div_add_mod m (d - 1)).symm
  rw [hq] at h
  simpa using h

theorem quotient_eq_one_upper_bound
    {d m : Nat} (hd2 : 2 ≤ d) (hq : m / (d - 1) = 1) :
    m ≤ 2 * d - 3 := by
  have hden : 0 < d - 1 := by omega
  have hr : m % (d - 1) < d - 1 := Nat.mod_lt m hden
  have hm_eq := eq_pred_add_mod_of_div_eq_one (d := d) (m := m) hq
  omega

theorem quotient_eq_one_range_of_mqr
    {d m q r : Nat}
    (hmqr : m = (d - 1) * q + r)
    (hrlt : r < d - 1) (hrpos : 0 < r) (hq : q = 1) :
    d ≤ m ∧ m ≤ 2 * d - 3 := by
  subst q
  constructor <;> omega

theorem quotient_eq_one_m_eq_pred_add
    {d m q r : Nat}
    (hmqr : m = (d - 1) * q + r) (hq : q = 1) :
    m = d - 1 + r := by
  subst q
  omega

/--
A signed prefix-count certificate.

`diff i k` is intended to be `step i k - delta i`.  The remaining fields are
the algebraic side conditions needed before conversion to an admissible
prefix-count matrix.
-/
structure SignedPrefixCounts (d m : Nat) where
  zero : Fin d → Nat
  delta : Fin d → Nat
  diff : Fin d → Fin (d - 2) → Int
  diff_signed : ∀ i k, IsSignedVal (diff i k)
  step_nonneg : ∀ i k, 0 ≤ (delta i : Int) + diff i k
  row_eq :
    ∀ i : Fin d,
      (zero i : Int)
        + (((d - 1 : Nat) : Int) * (delta i : Int))
        + (∑ k : Fin (d - 2), diff i k)
        = (m : Int)
  col_zero :
    (∑ i : Fin d, zero i) = m
  col_delta :
    (∑ i : Fin d, delta i) = m
  diff_col_zero :
    ∀ k : Fin (d - 2), (∑ i : Fin d, diff i k) = 0
  prim_zero :
    ∀ i : Fin d, Nat.Coprime (zero i) m

namespace SignedPrefixCounts

def toParts {d m : Nat} (S : SignedPrefixCounts d m) : Parts d where
  zero := S.zero
  delta := S.delta
  step := fun i k => Int.toNat ((S.delta i : Int) + S.diff i k)

@[simp] theorem toParts_zero {d m : Nat}
    (S : SignedPrefixCounts d m) (i : Fin d) :
    S.toParts.zero i = S.zero i :=
  rfl

@[simp] theorem toParts_delta {d m : Nat}
    (S : SignedPrefixCounts d m) (i : Fin d) :
    S.toParts.delta i = S.delta i :=
  rfl

@[simp] theorem toParts_step {d m : Nat}
    (S : SignedPrefixCounts d m) (i : Fin d) (k : Fin (d - 2)) :
    S.toParts.step i k = Int.toNat ((S.delta i : Int) + S.diff i k) :=
  rfl

theorem diff_coprime {d m : Nat} (S : SignedPrefixCounts d m)
    (hm : Odd m) (i : Fin d) (k : Fin (d - 2)) :
    IntCoprime (S.diff i k) m :=
  signedVal_coprime_of_odd (S.diff_signed i k) hm

theorem toParts_step_int {d m : Nat} (S : SignedPrefixCounts d m)
    (i : Fin d) (k : Fin (d - 2)) :
    (S.toParts.step i k : Int) = (S.delta i : Int) + S.diff i k := by
  simp [toParts, Int.toNat_of_nonneg (S.step_nonneg i k)]

theorem toParts_row_sum {d m : Nat} (S : SignedPrefixCounts d m)
    (hd2 : 2 ≤ d) (i : Fin d) :
    S.toParts.zero i + S.toParts.delta i
      + (∑ k : Fin (d - 2), S.toParts.step i k) = m := by
  apply Int.ofNat.inj
  calc
    (((S.toParts.zero i + S.toParts.delta i
        + (∑ k : Fin (d - 2), S.toParts.step i k) : Nat) : Int))
        = (S.zero i : Int) + (S.delta i : Int)
          + (∑ k : Fin (d - 2), ((S.toParts.step i k : Nat) : Int)) := by
            simp
    _ = (S.zero i : Int) + (S.delta i : Int)
          + (∑ k : Fin (d - 2), ((S.delta i : Int) + S.diff i k)) := by
            simp_rw [S.toParts_step_int]
    _ = (S.zero i : Int)
          + (((d - 1 : Nat) : Int) * (S.delta i : Int))
          + (∑ k : Fin (d - 2), S.diff i k) := by
            rw [Finset.sum_add_distrib]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            have hdsub :
                (((d - 1 : Nat) : Int)) = (((d - 2 : Nat) : Int)) + 1 := by
              omega
            rw [hdsub]
            ring
    _ = (m : Int) := S.row_eq i

theorem toParts_col_step {d m : Nat} (S : SignedPrefixCounts d m)
    (k : Fin (d - 2)) :
    (∑ i : Fin d, S.toParts.step i k) = m := by
  apply Int.ofNat.inj
  calc
    (((∑ i : Fin d, S.toParts.step i k) : Nat) : Int)
        = (∑ i : Fin d, ((S.toParts.step i k : Nat) : Int)) := by
          simp
    _ = (∑ i : Fin d, ((S.delta i : Int) + S.diff i k)) := by
          simp_rw [S.toParts_step_int]
    _ = (∑ i : Fin d, (S.delta i : Int)) + (∑ i : Fin d, S.diff i k) := by
          rw [Finset.sum_add_distrib]
    _ = (m : Int) := by
          have hdelta : (∑ i : Fin d, (S.delta i : Int)) = (m : Int) := by
            exact_mod_cast S.col_delta
          rw [hdelta, S.diff_col_zero k]
          simp

theorem toParts_prim_step {d m : Nat} (S : SignedPrefixCounts d m)
    (hm : Odd m) (i : Fin d) (k : Fin (d - 2)) :
    IntCoprime ((S.toParts.step i k : Int) - (S.toParts.delta i : Int)) m := by
  have hstep := S.toParts_step_int i k
  have hdiff :
      (S.toParts.step i k : Int) - (S.toParts.delta i : Int) = S.diff i k := by
    rw [hstep]
    simp
  rw [hdiff]
  exact signedVal_coprime_of_odd (S.diff_signed i k) hm

theorem toParts_admissible {d m : Nat} (S : SignedPrefixCounts d m)
    (hd2 : 2 ≤ d) (hm : Odd m) :
    S.toParts.Admissible m where
  row_sum := S.toParts_row_sum hd2
  col_zero := S.col_zero
  col_delta := S.col_delta
  col_step := S.toParts_col_step
  prim_zero := S.prim_zero
  prim_step := S.toParts_prim_step hm

end SignedPrefixCounts

/--
Algebraic transportation data for the high-modulus branch, before it is turned
into signed prefix counts.  The fields match the decomposition
`m = (d - 1) * q + r`.
-/
structure QuotientTransport (d m q r : Nat) where
  zero : Fin d → Nat
  tau : Fin d → Int
  eps : Fin d → Fin (d - 2) → Int
  eps_signed : ∀ i k, IsSignedVal (eps i k)
  eps_col_zero : ∀ k : Fin (d - 2), (∑ i : Fin d, eps i k) = 0
  tau_sum : (∑ i : Fin d, tau i) = (q : Int) - (r : Int)
  delta_nonneg : ∀ i : Fin d, 0 ≤ (q : Int) - tau i
  step_nonneg : ∀ i k, 0 ≤ (q : Int) - tau i + eps i k
  zero_eq :
    ∀ i : Fin d,
      (zero i : Int)
        = (r : Int)
          + (((d - 1 : Nat) : Int) * tau i)
          - (∑ k : Fin (d - 2), eps i k)
  prim_zero : ∀ i : Fin d, Nat.Coprime (zero i) m

namespace QuotientTransport

def delta {d m q r : Nat} (T : QuotientTransport d m q r)
    (i : Fin d) : Nat :=
  Int.toNat ((q : Int) - T.tau i)

theorem delta_int {d m q r : Nat} (T : QuotientTransport d m q r)
    (i : Fin d) :
    (T.delta i : Int) = (q : Int) - T.tau i := by
  simp [delta, Int.toNat_of_nonneg (T.delta_nonneg i)]

theorem step_nonneg_delta {d m q r : Nat} (T : QuotientTransport d m q r)
    (i : Fin d) (k : Fin (d - 2)) :
    0 ≤ (T.delta i : Int) + T.eps i k := by
  rw [T.delta_int i]
  exact T.step_nonneg i k

theorem row_eq_signed {d m q r : Nat} (T : QuotientTransport d m q r)
    (hmqr : m = (d - 1) * q + r) (i : Fin d) :
    (T.zero i : Int)
      + (((d - 1 : Nat) : Int) * (T.delta i : Int))
      + (∑ k : Fin (d - 2), T.eps i k)
      = (m : Int) := by
  rw [T.zero_eq i, T.delta_int i]
  have hmqrInt :
      (m : Int) = (((d - 1 : Nat) : Int) * (q : Int)) + (r : Int) := by
    rw [hmqr]
    norm_num [Nat.cast_add, Nat.cast_mul]
  rw [hmqrInt]
  ring

theorem col_delta_signed {d m q r : Nat} (T : QuotientTransport d m q r)
    (hdpos : 0 < d) (hmqr : m = (d - 1) * q + r) :
    (∑ i : Fin d, T.delta i) = m := by
  apply Int.ofNat.inj
  calc
    (((∑ i : Fin d, T.delta i) : Nat) : Int)
        = (∑ i : Fin d, (T.delta i : Int)) := by
          simp
    _ = (∑ i : Fin d, ((q : Int) - T.tau i)) := by
          simp_rw [T.delta_int]
    _ = ((d : Int) * (q : Int)) - ((q : Int) - (r : Int)) := by
          rw [Finset.sum_sub_distrib, T.tau_sum]
          simp [Finset.sum_const]
    _ = (m : Int) := by
          have hmqrInt :
              (m : Int) = (((d - 1 : Nat) : Int) * (q : Int)) + (r : Int) := by
            rw [hmqr]
            norm_num [Nat.cast_add, Nat.cast_mul]
          rw [hmqrInt]
          have hdsub : (d : Int) = ((d - 1 : Nat) : Int) + 1 := by
            omega
          rw [hdsub]
          ring

theorem col_zero_signed {d m q r : Nat} (T : QuotientTransport d m q r)
    (hdpos : 0 < d) (hmqr : m = (d - 1) * q + r) :
    (∑ i : Fin d, T.zero i) = m := by
  apply Int.ofNat.inj
  calc
    (((∑ i : Fin d, T.zero i) : Nat) : Int)
        = (∑ i : Fin d, (T.zero i : Int)) := by
          simp
    _ = (∑ i : Fin d,
          ((r : Int) + (((d - 1 : Nat) : Int) * T.tau i)
            - (∑ k : Fin (d - 2), T.eps i k))) := by
          simp_rw [T.zero_eq]
    _ = (d : Int) * (r : Int)
          + (((d - 1 : Nat) : Int) * ((q : Int) - (r : Int))) - 0 := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
          have htau :
              (∑ i : Fin d, ((d - 1 : Nat) : Int) * T.tau i)
                = ((d - 1 : Nat) : Int) * ((q : Int) - (r : Int)) := by
            rw [← Finset.mul_sum, T.tau_sum]
          have heps :
              (∑ i : Fin d, ∑ k : Fin (d - 2), T.eps i k) = 0 := by
            rw [Finset.sum_comm]
            simp [T.eps_col_zero]
          rw [htau, heps]
          simp [Finset.sum_const]
    _ = (m : Int) := by
          have hmqrInt :
              (m : Int) = (((d - 1 : Nat) : Int) * (q : Int)) + (r : Int) := by
            rw [hmqr]
            norm_num [Nat.cast_add, Nat.cast_mul]
          rw [hmqrInt]
          have hdsub : (d : Int) = ((d - 1 : Nat) : Int) + 1 := by
            omega
          rw [hdsub]
          ring

def toSigned {d m q r : Nat} (T : QuotientTransport d m q r)
    (hdpos : 0 < d) (hmqr : m = (d - 1) * q + r) :
    SignedPrefixCounts d m where
  zero := T.zero
  delta := T.delta
  diff := T.eps
  diff_signed := T.eps_signed
  step_nonneg := T.step_nonneg_delta
  row_eq := T.row_eq_signed hmqr
  col_zero := T.col_zero_signed hdpos hmqr
  col_delta := T.col_delta_signed hdpos hmqr
  diff_col_zero := T.eps_col_zero
  prim_zero := T.prim_zero

theorem toSigned_admissible {d m q r : Nat}
    (T : QuotientTransport d m q r)
    (hd2 : 2 ≤ d) (hmodd : Odd m)
    (hmqr : m = (d - 1) * q + r) :
    (T.toSigned (by omega) hmqr).toParts.Admissible m :=
  (T.toSigned (by omega) hmqr).toParts_admissible hd2 hmodd

end QuotientTransport

def TransportQge2Goal : Prop :=
  ∀ {d m q r : Nat},
    Odd d → 5 ≤ d → Odd m →
    m = (d - 1) * q + r →
    r < d - 1 → 0 < r → 2 ≤ q →
    Nonempty (QuotientTransport d m q r)

def TransportQeq1Goal : Prop :=
  ∀ {d m q r : Nat},
    Odd d → 5 ≤ d → Odd m →
    m = (d - 1) * q + r →
    r < d - 1 → 0 < r → q = 1 →
    Nonempty (QuotientTransport d m q r)

def AdmissiblePartsCountBranchGoal : Prop :=
  ∀ {d m : Nat}, Odd d → Odd m → 5 ≤ d → d ≤ m →
    ∃ C : Parts d, C.Admissible m

theorem admissiblePartsCountBranchGoal_of_transports
    (hQge2 : TransportQge2Goal)
    (hQeq1 : TransportQeq1Goal) :
    AdmissiblePartsCountBranchGoal := by
  intro d m hdodd hmodd hd5 hdm
  have hd2 : 2 ≤ d := by omega
  rcases quotient_remainder_count_branch hdodd hmodd hd2 hdm with
    ⟨hmqr, hrlt, hrpos, hq⟩
  rcases hq with hq1 | hq2
  · rcases hQeq1 hdodd hd5 hmodd hmqr hrlt hrpos hq1 with ⟨T⟩
    exact ⟨(T.toSigned (by omega) hmqr).toParts,
      T.toSigned_admissible hd2 hmodd hmqr⟩
  · rcases hQge2 hdodd hd5 hmodd hmqr hrlt hrpos hq2 with ⟨T⟩
    exact ⟨(T.toSigned (by omega) hmqr).toParts,
      T.toSigned_admissible hd2 hmodd hmqr⟩

/--
Row-wise margin data for the signed transportation branch.

The field `sigma` is the desired row sum of the signed correction matrix
`eps`.  The identity `sigma_def` is arranged so that a signed matrix with row
sum `sigma` gives exactly the `zero_eq` field of `QuotientTransport`.
-/
structure MarginPlan (d m q r : Nat) where
  zero : Fin d → Nat
  tau : Fin d → Int
  sigma : Fin d → Int
  sigma_def :
    ∀ i : Fin d,
      sigma i =
        (r : Int)
          + (((d - 1 : Nat) : Int) * tau i)
          - (zero i : Int)
  tau_sum : (∑ i : Fin d, tau i) = (q : Int) - (r : Int)
  delta_nonneg : ∀ i : Fin d, 0 ≤ (q : Int) - tau i
  prim_zero : ∀ i : Fin d, Nat.Coprime (zero i) m

/--
A signed correction matrix with entries in `{ -2, -1, 1, 2 }`, prescribed row
sums, and zero column sums.
-/
structure SignedMarginMatrix (d : Nat) (sigma : Fin d → Int) where
  eps : Fin d → Fin (d - 2) → Int
  eps_signed : ∀ i k, IsSignedVal (eps i k)
  row_sum : ∀ i : Fin d, (∑ k : Fin (d - 2), eps i k) = sigma i
  col_sum : ∀ k : Fin (d - 2), (∑ i : Fin d, eps i k) = 0

namespace SignedMarginMatrix

theorem eps_ge_neg_two {d : Nat} {sigma : Fin d → Int}
    (E : SignedMarginMatrix d sigma) (i : Fin d) (k : Fin (d - 2)) :
    (-2 : Int) ≤ E.eps i k :=
  signedVal_ge_neg_two (E.eps_signed i k)

theorem eps_le_two {d : Nat} {sigma : Fin d → Int}
    (E : SignedMarginMatrix d sigma) (i : Fin d) (k : Fin (d - 2)) :
    E.eps i k ≤ (2 : Int) :=
  signedVal_le_two (E.eps_signed i k)

theorem neg_two_mul_le_row_sum {d : Nat} {sigma : Fin d → Int}
    (E : SignedMarginMatrix d sigma) (i : Fin d) :
    -((2 * (d - 2) : Nat) : Int) ≤ sigma i := by
  have hsum :
      (∑ _k : Fin (d - 2), (-2 : Int))
        ≤ ∑ k : Fin (d - 2), E.eps i k := by
    apply Finset.sum_le_sum
    intro k _hk
    exact E.eps_ge_neg_two i k
  have hconst :
      (∑ _k : Fin (d - 2), (-2 : Int))
        = -((2 * (d - 2) : Nat) : Int) := by
    simp [Finset.sum_const]
    omega
  rw [hconst] at hsum
  simpa [E.row_sum i] using hsum

theorem row_sum_le_two_mul {d : Nat} {sigma : Fin d → Int}
    (E : SignedMarginMatrix d sigma) (i : Fin d) :
    sigma i ≤ ((2 * (d - 2) : Nat) : Int) := by
  have hsum :
      (∑ k : Fin (d - 2), E.eps i k)
        ≤ ∑ _k : Fin (d - 2), (2 : Int) := by
    apply Finset.sum_le_sum
    intro k _hk
    exact E.eps_le_two i k
  have hconst :
      (∑ _k : Fin (d - 2), (2 : Int))
        = ((2 * (d - 2) : Nat) : Int) := by
    simp [Finset.sum_const]
    omega
  rw [hconst] at hsum
  simpa [E.row_sum i] using hsum

theorem sigma_sum_eq_zero {d : Nat} {sigma : Fin d → Int}
    (E : SignedMarginMatrix d sigma) :
    (∑ i : Fin d, sigma i) = 0 := by
  calc
    (∑ i : Fin d, sigma i)
        = ∑ i : Fin d, ∑ k : Fin (d - 2), E.eps i k := by
            simp [E.row_sum]
    _ = ∑ k : Fin (d - 2), ∑ i : Fin d, E.eps i k := by
            rw [Finset.sum_comm]
    _ = 0 := by
            simp [E.col_sum]

end SignedMarginMatrix

namespace MarginPlan

theorem delta_eq_zero_iff {d m q r : Nat}
    (P : MarginPlan d m q r) (i : Fin d) :
    (q : Int) - P.tau i = 0 ↔ P.tau i = (q : Int) := by
  constructor <;> intro h <;> linarith

theorem delta_eq_one_iff {d m q r : Nat}
    (P : MarginPlan d m q r) (i : Fin d) :
    (q : Int) - P.tau i = 1 ↔ P.tau i = (q : Int) - 1 := by
  constructor <;> intro h <;> linarith

theorem tau_le_q {d m q r : Nat}
    (P : MarginPlan d m q r) (i : Fin d) :
    P.tau i ≤ (q : Int) := by
  have hdelta := P.delta_nonneg i
  linarith

theorem sigma_sum_eq {d m q r : Nat}
    (P : MarginPlan d m q r)
    (hdpos : 0 < d)
    (hmqr : m = (d - 1) * q + r) :
    (∑ i : Fin d, P.sigma i)
      = (m : Int) - (∑ i : Fin d, (P.zero i : Int)) := by
  calc
    (∑ i : Fin d, P.sigma i)
        = ∑ i : Fin d,
            ((r : Int)
              + (((d - 1 : Nat) : Int) * P.tau i)
              - (P.zero i : Int)) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact P.sigma_def i
    _ = (d : Int) * (r : Int)
          + (((d - 1 : Nat) : Int) * ((q : Int) - (r : Int)))
          - (∑ i : Fin d, (P.zero i : Int)) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
            have htau :
                (∑ i : Fin d, ((d - 1 : Nat) : Int) * P.tau i)
                  = ((d - 1 : Nat) : Int) * ((q : Int) - (r : Int)) := by
              rw [← Finset.mul_sum, P.tau_sum]
            rw [htau]
            simp [Finset.sum_const]
    _ = (m : Int) - (∑ i : Fin d, (P.zero i : Int)) := by
            have hmqrInt :
                (m : Int) =
                  (((d - 1 : Nat) : Int) * (q : Int)) + (r : Int) := by
              rw [hmqr]
              norm_num [Nat.cast_add, Nat.cast_mul]
            rw [hmqrInt]
            have hdsub : (d : Int) = ((d - 1 : Nat) : Int) + 1 := by
              omega
            rw [hdsub]
            ring

theorem sigma_sum_eq_zero_of_zero_sum {d m q r : Nat}
    (P : MarginPlan d m q r)
    (hdpos : 0 < d)
    (hmqr : m = (d - 1) * q + r)
    (hzero : (∑ i : Fin d, P.zero i) = m) :
    (∑ i : Fin d, P.sigma i) = 0 := by
  have hzeroInt : (∑ i : Fin d, (P.zero i : Int)) = (m : Int) := by
    exact_mod_cast hzero
  rw [P.sigma_sum_eq hdpos hmqr, hzeroInt]
  simp

/--
Combine a row margin plan and a signed correction matrix into the quotient
transport data consumed by `QuotientTransport.toSigned_admissible`.
-/
def toTransport {d m q r : Nat}
    (P : MarginPlan d m q r)
    (E : SignedMarginMatrix d P.sigma)
    (hstep : ∀ i k, 0 ≤ (q : Int) - P.tau i + E.eps i k) :
    QuotientTransport d m q r where
  zero := P.zero
  tau := P.tau
  eps := E.eps
  eps_signed := E.eps_signed
  eps_col_zero := E.col_sum
  tau_sum := P.tau_sum
  delta_nonneg := P.delta_nonneg
  step_nonneg := hstep
  zero_eq := by
    intro i
    have hsigma := P.sigma_def i
    have hrow := E.row_sum i
    linarith
  prim_zero := P.prim_zero

end MarginPlan

structure Qge2PlanBounds {d m q r : Nat}
    (P : MarginPlan d m q r) : Prop where
  delta_ge_two : ∀ i : Fin d, (2 : Int) ≤ (q : Int) - P.tau i

namespace Qge2PlanBounds

theorem step_nonneg {d m q r : Nat}
    {P : MarginPlan d m q r} (hP : Qge2PlanBounds P)
    {E : SignedMarginMatrix d P.sigma} :
    ∀ i k, 0 ≤ (q : Int) - P.tau i + E.eps i k := by
  intro i k
  have hdelta := hP.delta_ge_two i
  have heps := E.eps_ge_neg_two i k
  linarith

theorem tau_le_q_sub_two {d m q r : Nat}
    {P : MarginPlan d m q r} (hP : Qge2PlanBounds P) (i : Fin d) :
    P.tau i ≤ (q : Int) - 2 := by
  have hdelta := hP.delta_ge_two i
  linarith

theorem tau_sum_le {d m q r : Nat}
    {P : MarginPlan d m q r} (hP : Qge2PlanBounds P) :
    (q : Int) - (r : Int) ≤ (d : Int) * ((q : Int) - 2) := by
  have hsum :
      (∑ i : Fin d, P.tau i) ≤ ∑ _i : Fin d, ((q : Int) - 2) := by
    apply Finset.sum_le_sum
    intro i _hi
    exact hP.tau_le_q_sub_two i
  have hconst :
      (∑ _i : Fin d, ((q : Int) - 2)) =
        (d : Int) * ((q : Int) - 2) := by
    simp [Finset.sum_const]
    ring
  rw [P.tau_sum, hconst] at hsum
  exact hsum

theorem not_for_q_two_r_one {d m : Nat}
    {P : MarginPlan d m 2 1} (hP : Qge2PlanBounds P) : False := by
  have hsum := hP.tau_sum_le
  norm_num at hsum

end Qge2PlanBounds

structure StepNonnegCompatibility {d m q r : Nat}
    (P : MarginPlan d m q r) (E : SignedMarginMatrix d P.sigma) : Prop where
  eps_nonneg_of_delta_zero :
    ∀ i k, (q : Int) - P.tau i = 0 → 0 ≤ E.eps i k
  eps_ge_neg_one_of_delta_one :
    ∀ i k, (q : Int) - P.tau i = 1 → (-1 : Int) ≤ E.eps i k

namespace StepNonnegCompatibility

theorem of_step_nonneg {d m q r : Nat}
    {P : MarginPlan d m q r} {E : SignedMarginMatrix d P.sigma}
    (hstep : ∀ i k, 0 ≤ (q : Int) - P.tau i + E.eps i k) :
    StepNonnegCompatibility P E where
  eps_nonneg_of_delta_zero := by
    intro i k hdelta
    have h := hstep i k
    linarith
  eps_ge_neg_one_of_delta_one := by
    intro i k hdelta
    have h := hstep i k
    linarith

theorem step_nonneg {d m q r : Nat}
    {P : MarginPlan d m q r} {E : SignedMarginMatrix d P.sigma}
    (hCompat : StepNonnegCompatibility P E) :
    ∀ i k, 0 ≤ (q : Int) - P.tau i + E.eps i k := by
  intro i k
  have hdelta_nonneg := P.delta_nonneg i
  by_cases h0 : (q : Int) - P.tau i = 0
  · have heps := hCompat.eps_nonneg_of_delta_zero i k h0
    linarith
  · by_cases h1 : (q : Int) - P.tau i = 1
    · have heps := hCompat.eps_ge_neg_one_of_delta_one i k h1
      linarith
    · have hdelta_ge_two : (2 : Int) ≤ (q : Int) - P.tau i := by
        omega
      have heps := E.eps_ge_neg_two i k
      linarith

end StepNonnegCompatibility

/--
A base matrix with only `±1` entries and column sums `-1`.  The q=1 branch can
upgrade one explicit `+1` in each column to `+2`, producing signed column sums
zero without using an abstract matching theorem at this layer.
-/
structure PMOneBase (d : Nat) where
  entry : Fin d → Fin (d - 2) → Int
  entry_pm_one : ∀ i k, entry i k = (-1 : Int) ∨ entry i k = 1
  col_sum_neg_one : ∀ k : Fin (d - 2), (∑ i : Fin d, entry i k) = (-1 : Int)

namespace PMOneBase

theorem sum_if_mem_one_neg_one {d : Nat} (s : Finset (Fin d)) :
    (∑ i : Fin d, if i ∈ s then (1 : Int) else (-1 : Int))
      = (2 * (s.card : Int)) - (d : Int) := by
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (Fin d))) (p := fun i => i ∈ s)
    (f := fun i => if i ∈ s then (1 : Int) else (-1 : Int))]
  have hfilter : (Finset.univ.filter (fun i : Fin d => i ∈ s)) = s := by
    ext i
    simp
  have hfilterNotCard :
      (Finset.univ.filter (fun i : Fin d => i ∉ s)).card = d - s.card := by
    have hcomp : (Finset.univ.filter (fun i : Fin d => i ∉ s)) = sᶜ := by
      ext i
      simp
    rw [hcomp, Finset.card_compl, Fintype.card_fin]
  rw [hfilter]
  have hsum_s :
      (∑ x ∈ s, if x ∈ s then (1 : Int) else (-1 : Int))
        = (s.card : Int) := by
    calc
      (∑ x ∈ s, if x ∈ s then (1 : Int) else (-1 : Int))
          = ∑ _x ∈ s, (1 : Int) := by
              apply Finset.sum_congr rfl
              intro x hx
              simp [hx]
      _ = (s.card : Int) := by
              simp
  have hsum_not :
      (∑ x with x ∉ s, if x ∈ s then (1 : Int) else (-1 : Int))
        = -((d - s.card : Nat) : Int) := by
    calc
      (∑ x with x ∉ s, if x ∈ s then (1 : Int) else (-1 : Int))
          = ∑ _x ∈ (Finset.univ.filter (fun x : Fin d => x ∉ s)),
              (-1 : Int) := by
              apply Finset.sum_congr rfl
              intro x hx
              have hxnot : x ∉ s := by
                simpa using hx
              simp [hxnot]
      _ = -((Finset.univ.filter (fun x : Fin d => x ∉ s)).card : Int) := by
              simp
      _ = -((d - s.card : Nat) : Int) := by
              rw [hfilterNotCard]
  rw [hsum_s, hsum_not]
  have hcard_le : s.card ≤ d := by
    calc
      s.card ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_le_univ s
      _ = d := by simp
  omega

theorem sum_if_mem_one_neg_one_eq_neg_one_of_card_half {d : Nat}
    (hdodd : Odd d) {s : Finset (Fin d)}
    (hcard : s.card = (d - 1) / 2) :
    (∑ i : Fin d, if i ∈ s then (1 : Int) else (-1 : Int)) = (-1 : Int) := by
  rw [sum_if_mem_one_neg_one, hcard]
  rcases hdodd with ⟨a, ha⟩
  omega

theorem exists_finset_card_eq_and_mem {α : Type*}
    [Fintype α] (a : α) {n : Nat}
    (hpos : 1 ≤ n) (hle : n ≤ Fintype.card α) :
    ∃ s : Finset α, a ∈ s ∧ s.card = n := by
  classical
  have hauniv : a ∈ (Finset.univ : Finset α) := by
    simp
  have hcardErase :
      ((Finset.univ : Finset α).erase a).card = Fintype.card α - 1 := by
    rw [Finset.card_erase_of_mem hauniv, Finset.card_univ]
  have hsub : n - 1 ≤ ((Finset.univ : Finset α).erase a).card := by
    rw [hcardErase]
    omega
  rcases Finset.exists_subset_card_eq hsub with ⟨t, ht_subset, ht_card⟩
  refine ⟨insert a t, by simp, ?_⟩
  have hnot : a ∉ t := by
    intro hat
    have : a ∈ (Finset.univ : Finset α).erase a := ht_subset hat
    simp at this
  rw [Finset.card_insert_of_notMem hnot, ht_card]
  omega

structure PlusFamily (d : Nat) where
  plus : Fin (d - 2) → Finset (Fin d)
  plus_card : ∀ k : Fin (d - 2), (plus k).card = (d - 1) / 2
  mate : Fin (d - 2) → Fin d
  mate_injective : Function.Injective mate
  mate_mem : ∀ k : Fin (d - 2), mate k ∈ plus k

structure PlusOneMatching {d : Nat} (B : PMOneBase d) where
  mate : Fin (d - 2) → Fin d
  injective : Function.Injective mate
  pos : ∀ k : Fin (d - 2), B.entry (mate k) k = 1

namespace PlusFamily

def rowPlusSet {d : Nat} (F : PlusFamily d) (i : Fin d) :
    Finset (Fin (d - 2)) :=
  Finset.univ.filter (fun k : Fin (d - 2) => i ∈ F.plus k)

def rowMateSet {d : Nat} (F : PlusFamily d) (i : Fin d) :
    Finset (Fin (d - 2)) :=
  Finset.univ.filter (fun k : Fin (d - 2) => i = F.mate k)

theorem nonempty {d : Nat} (hdodd : Odd d) (hd5 : 5 ≤ d) :
    Nonempty (PlusFamily d) := by
  classical
  let n := (d - 1) / 2
  let mate : Fin (d - 2) → Fin d := fun k => ⟨k.val, by omega⟩
  have hmate_injective : Function.Injective mate := by
    intro k l h
    apply Fin.ext
    change k.val = l.val
    simpa [mate] using congrArg Fin.val h
  have hnpos : 1 ≤ n := by
    rcases hdodd with ⟨a, ha⟩
    omega
  have hnle : n ≤ Fintype.card (Fin d) := by
    simp [n]
    omega
  have hexists :
      ∀ k : Fin (d - 2), ∃ s : Finset (Fin d), mate k ∈ s ∧ s.card = n := by
    intro k
    exact exists_finset_card_eq_and_mem (mate k) hnpos hnle
  choose plus hplus using hexists
  exact ⟨{
    plus := plus
    plus_card := by
      intro k
      simpa [n] using (hplus k).2
    mate := mate
    mate_injective := hmate_injective
    mate_mem := by
      intro k
      exact (hplus k).1
  }⟩

def toBase {d : Nat} (F : PlusFamily d) (hdodd : Odd d) : PMOneBase d where
  entry := fun i k => if i ∈ F.plus k then (1 : Int) else (-1 : Int)
  entry_pm_one := by
    intro i k
    by_cases h : i ∈ F.plus k
    · simp [h]
    · simp [h]
  col_sum_neg_one := by
    intro k
    exact sum_if_mem_one_neg_one_eq_neg_one_of_card_half
      hdodd (F.plus_card k)

def toMatching {d : Nat} (F : PlusFamily d) (hdodd : Odd d) :
    PlusOneMatching (F.toBase hdodd) where
  mate := F.mate
  injective := F.mate_injective
  pos := by
    intro k
    simp [toBase, F.mate_mem k]

theorem base_row_sum {d : Nat} (F : PlusFamily d)
    (hdodd : Odd d) (i : Fin d) :
    (∑ k : Fin (d - 2), (F.toBase hdodd).entry i k)
      =
      (2 * ((F.rowPlusSet i).card : Int)) - ((d - 2 : Nat) : Int) := by
  calc
    (∑ k : Fin (d - 2), (F.toBase hdodd).entry i k)
        = ∑ k : Fin (d - 2),
            if k ∈ F.rowPlusSet i then (1 : Int) else (-1 : Int) := by
            apply Finset.sum_congr rfl
            intro k _hk
            simp [toBase, rowPlusSet]
    _ = (2 * ((F.rowPlusSet i).card : Int)) - ((d - 2 : Nat) : Int) := by
            exact sum_if_mem_one_neg_one (F.rowPlusSet i)

theorem toBase_entry_nonneg_iff {d : Nat} (F : PlusFamily d)
    (hdodd : Odd d) (i : Fin d) (k : Fin (d - 2)) :
    0 ≤ (F.toBase hdodd).entry i k ↔ i ∈ F.plus k := by
  by_cases h : i ∈ F.plus k
  · simp [toBase, h]
  · simp [toBase, h]

end PlusFamily

def upgrade {d : Nat} (B : PMOneBase d) (μ : PlusOneMatching B)
    (i : Fin d) (k : Fin (d - 2)) : Int :=
  B.entry i k + if i = μ.mate k then (1 : Int) else 0

theorem upgrade_eq_two_of_mate {d : Nat} (B : PMOneBase d)
    (μ : PlusOneMatching B) (k : Fin (d - 2)) :
    B.upgrade μ (μ.mate k) k = 2 := by
  simp [upgrade, μ.pos k]

theorem upgrade_eq_entry_of_ne {d : Nat} (B : PMOneBase d)
    (μ : PlusOneMatching B) {i : Fin d} {k : Fin (d - 2)}
    (h : i ≠ μ.mate k) :
    B.upgrade μ i k = B.entry i k := by
  simp [upgrade, h]

theorem upgrade_signed {d : Nat} (B : PMOneBase d)
    (μ : PlusOneMatching B) (i : Fin d) (k : Fin (d - 2)) :
    IsSignedVal (B.upgrade μ i k) := by
  by_cases h : i = μ.mate k
  · subst i
    simp [upgrade, μ.pos k, IsSignedVal, signedVals]
  · rcases B.entry_pm_one i k with hneg | hpos
    · simp [upgrade, h, hneg, IsSignedVal, signedVals]
    · simp [upgrade, h, hpos, IsSignedVal, signedVals]

theorem upgrade_col_sum_zero {d : Nat} (B : PMOneBase d)
    (μ : PlusOneMatching B) (k : Fin (d - 2)) :
    (∑ i : Fin d, B.upgrade μ i k) = 0 := by
  calc
    (∑ i : Fin d, B.upgrade μ i k)
        = (∑ i : Fin d, B.entry i k)
            + ∑ i : Fin d, (if i = μ.mate k then (1 : Int) else 0) := by
            simp [upgrade, Finset.sum_add_distrib]
    _ = (-1 : Int) + 1 := by
            simp [B.col_sum_neg_one k]
    _ = 0 := by norm_num

theorem upgrade_row_sum {d : Nat} (B : PMOneBase d)
    (μ : PlusOneMatching B) (i : Fin d) :
    (∑ k : Fin (d - 2), B.upgrade μ i k)
      =
      (∑ k : Fin (d - 2), B.entry i k)
        + ∑ k : Fin (d - 2), (if i = μ.mate k then (1 : Int) else 0) := by
  simp [upgrade, Finset.sum_add_distrib]

theorem mate_indicator_sum_eq_one {d : Nat} (B : PMOneBase d)
    (μ : PlusOneMatching B) (k : Fin (d - 2)) :
    (∑ l : Fin (d - 2),
      if μ.mate k = μ.mate l then (1 : Int) else 0) = 1 := by
  calc
    (∑ l : Fin (d - 2),
      if μ.mate k = μ.mate l then (1 : Int) else 0)
        = ∑ l : Fin (d - 2), if k = l then (1 : Int) else 0 := by
            apply Finset.sum_congr rfl
            intro l _hl
            by_cases h : k = l
            · subst l
              simp
            · have hmate : μ.mate k ≠ μ.mate l := by
                intro hmk
                exact h (μ.injective hmk)
              simp [h, hmate]
    _ = 1 := by simp

theorem upgrade_row_sum_of_mate {d : Nat} (B : PMOneBase d)
    (μ : PlusOneMatching B) (k : Fin (d - 2)) :
    (∑ l : Fin (d - 2), B.upgrade μ (μ.mate k) l)
      = (∑ l : Fin (d - 2), B.entry (μ.mate k) l) + 1 := by
  rw [B.upgrade_row_sum μ (μ.mate k), B.mate_indicator_sum_eq_one μ k]

namespace PlusFamily

theorem upgraded_row_sum {d : Nat} (F : PlusFamily d)
    (hdodd : Odd d) (i : Fin d) :
    (∑ k : Fin (d - 2), (F.toBase hdodd).upgrade (F.toMatching hdodd) i k)
      =
      (2 * ((F.rowPlusSet i).card : Int)) - ((d - 2 : Nat) : Int)
        + ((F.rowMateSet i).card : Int) := by
  rw [(F.toBase hdodd).upgrade_row_sum (F.toMatching hdodd) i,
    F.base_row_sum hdodd i]
  have hmateCard :
      (∑ k : Fin (d - 2), if i = F.mate k then (1 : Int) else 0)
        = ((F.rowMateSet i).card : Int) := by
    simp [rowMateSet]
  simp only [toMatching]
  exact congrArg
    (fun z : Int =>
      (2 * ((F.rowPlusSet i).card : Int)) - ((d - 2 : Nat) : Int) + z)
    hmateCard

theorem upgraded_row_sum_of_mate {d : Nat} (F : PlusFamily d)
    (hdodd : Odd d) (k : Fin (d - 2)) :
    (∑ l : Fin (d - 2),
      (F.toBase hdodd).upgrade (F.toMatching hdodd) (F.mate k) l)
      = (2 * ((F.rowPlusSet (F.mate k)).card : Int))
        - ((d - 2 : Nat) : Int) + 1 := by
  rw [F.upgraded_row_sum hdodd (F.mate k)]
  have hsumCard :
      (∑ l : Fin (d - 2), if F.mate k = F.mate l then (1 : Int) else 0)
        = ((F.rowMateSet (F.mate k)).card : Int) := by
    simp [rowMateSet]
  have hsumOne :
      (∑ l : Fin (d - 2), if F.mate k = F.mate l then (1 : Int) else 0)
        = 1 := by
    simpa only [toMatching] using
      (F.toBase hdodd).mate_indicator_sum_eq_one (F.toMatching hdodd) k
  have hcardInt : ((F.rowMateSet (F.mate k)).card : Int) = 1 := by
    linarith
  rw [hcardInt]

theorem rowMateSet_card_le_one {d : Nat} (F : PlusFamily d)
    (i : Fin d) :
    (F.rowMateSet i).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro k hk l hl
  have hik : i = F.mate k := by
    simpa [rowMateSet] using hk
  have hil : i = F.mate l := by
    simpa [rowMateSet] using hl
  exact F.mate_injective (hik.symm.trans hil)

theorem rowMateSet_card_eq_one_of_mate {d : Nat} (F : PlusFamily d)
    (k : Fin (d - 2)) :
    (F.rowMateSet (F.mate k)).card = 1 := by
  have hpos : 1 ≤ (F.rowMateSet (F.mate k)).card := by
    rw [Finset.one_le_card]
    exact ⟨k, by simp [rowMateSet]⟩
  exact Nat.le_antisymm (F.rowMateSet_card_le_one (F.mate k)) hpos

theorem rowMateSet_card_eq_zero_of_not_mate {d : Nat} (F : PlusFamily d)
    {i : Fin d} (hnot : ∀ k : Fin (d - 2), i ≠ F.mate k) :
    (F.rowMateSet i).card = 0 := by
  rw [Finset.card_eq_zero]
  ext k
  simp [rowMateSet, hnot k]

theorem upgraded_row_sum_of_not_mate {d : Nat} (F : PlusFamily d)
    (hdodd : Odd d) {i : Fin d}
    (hnot : ∀ k : Fin (d - 2), i ≠ F.mate k) :
    (∑ k : Fin (d - 2), (F.toBase hdodd).upgrade (F.toMatching hdodd) i k)
      = (2 * ((F.rowPlusSet i).card : Int)) - ((d - 2 : Nat) : Int) := by
  rw [F.upgraded_row_sum hdodd i, F.rowMateSet_card_eq_zero_of_not_mate hnot]
  simp

theorem upgraded_row_sum_ne_zero_of_not_mate {d : Nat} (F : PlusFamily d)
    (hdodd : Odd d) (hd5 : 5 ≤ d) {i : Fin d}
    (hnot : ∀ k : Fin (d - 2), i ≠ F.mate k) :
    (∑ k : Fin (d - 2), (F.toBase hdodd).upgrade (F.toMatching hdodd) i k)
      ≠ 0 := by
  intro hzero
  have hrow := F.upgraded_row_sum_of_not_mate hdodd hnot
  rw [hzero] at hrow
  have hInt :
      (2 * ((F.rowPlusSet i).card : Int)) = ((d - 2 : Nat) : Int) := by
    linarith
  have hNat : 2 * (F.rowPlusSet i).card = d - 2 := by
    exact_mod_cast hInt
  rcases hdodd with ⟨a, ha⟩
  omega

theorem exists_rowMateSet_card_eq_zero {d : Nat} (F : PlusFamily d)
    (hd5 : 5 ≤ d) :
    ∃ i : Fin d, (F.rowMateSet i).card = 0 := by
  classical
  by_contra hnot
  have hsurj : Function.Surjective F.mate := by
    intro i
    have hcard_ne : (F.rowMateSet i).card ≠ 0 := by
      intro hzero
      exact hnot ⟨i, hzero⟩
    have hnonempty : (F.rowMateSet i).Nonempty := by
      exact (Finset.card_ne_zero.mp hcard_ne)
    rcases hnonempty with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hik : i = F.mate k := by
      simpa [rowMateSet] using hk
    exact hik.symm
  have hle := Fintype.card_le_of_surjective F.mate hsurj
  simp at hle
  omega

theorem not_all_upgraded_row_sum_zero {d : Nat} (F : PlusFamily d)
    (hdodd : Odd d) (hd5 : 5 ≤ d) :
    ¬ ∀ i : Fin d,
      (∑ k : Fin (d - 2), (F.toBase hdodd).upgrade (F.toMatching hdodd) i k)
        = 0 := by
  classical
  intro hzero
  rcases F.exists_rowMateSet_card_eq_zero hd5 with ⟨i, hiMate⟩
  have hrow := F.upgraded_row_sum hdodd i
  rw [hzero i, hiMate] at hrow
  have hrow' :
      (0 : Int) =
        (2 * ((F.rowPlusSet i).card : Int)) - ((d - 2 : Nat) : Int) := by
    simpa only [Nat.cast_zero, add_zero] using hrow
  have hInt :
      (2 * ((F.rowPlusSet i).card : Int)) = ((d - 2 : Nat) : Int) := by
    linarith
  have hNat : 2 * (F.rowPlusSet i).card = d - 2 := by
    exact_mod_cast hInt
  rcases hdodd with ⟨a, ha⟩
  omega

end PlusFamily

theorem upgrade_ge_neg_one {d : Nat} (B : PMOneBase d)
    (μ : PlusOneMatching B) (i : Fin d) (k : Fin (d - 2)) :
    (-1 : Int) ≤ B.upgrade μ i k := by
  have hentry : (-1 : Int) ≤ B.entry i k := by
    rcases B.entry_pm_one i k with hneg | hpos
    · simp [hneg]
    · simp [hpos]
  have hind : 0 ≤ (if i = μ.mate k then (1 : Int) else 0) := by
    by_cases h : i = μ.mate k <;> simp [h]
  unfold upgrade
  linarith

theorem upgrade_nonneg_of_entry_nonneg {d : Nat} (B : PMOneBase d)
    (μ : PlusOneMatching B) {i : Fin d} {k : Fin (d - 2)}
    (hentry : 0 ≤ B.entry i k) :
    0 ≤ B.upgrade μ i k := by
  have hind : 0 ≤ (if i = μ.mate k then (1 : Int) else 0) := by
    by_cases h : i = μ.mate k <;> simp [h]
  unfold upgrade
  linarith

end PMOneBase

/--
The matched `±1` q=1 matrix after upgrading one explicit `+1` in every column.
The row-sum field is stated after upgrade so it can be consumed directly by
`SignedMarginMatrix`.
-/
structure MatchedPMOneMatrix (d : Nat) (sigma : Fin d → Int) where
  base : PMOneBase d
  matching : PMOneBase.PlusOneMatching base
  row_sum :
    ∀ i : Fin d,
      (∑ k : Fin (d - 2), base.upgrade matching i k) = sigma i

namespace MatchedPMOneMatrix

def eps {d : Nat} {sigma : Fin d → Int}
    (M : MatchedPMOneMatrix d sigma) :
    Fin d → Fin (d - 2) → Int :=
  M.base.upgrade M.matching

def toSignedMarginMatrix {d : Nat} {sigma : Fin d → Int}
    (M : MatchedPMOneMatrix d sigma) :
    SignedMarginMatrix d sigma where
  eps := M.eps
  eps_signed := M.base.upgrade_signed M.matching
  row_sum := M.row_sum
  col_sum := M.base.upgrade_col_sum_zero M.matching

theorem stepNonnegCompatibility {d m q r : Nat}
    {P : MarginPlan d m q r}
    (M : MatchedPMOneMatrix d P.sigma)
    (hZeroRows :
      ∀ i k, (q : Int) - P.tau i = 0 → 0 ≤ M.base.entry i k) :
    StepNonnegCompatibility P M.toSignedMarginMatrix where
  eps_nonneg_of_delta_zero := by
    intro i k hdelta
    have hentry := hZeroRows i k hdelta
    simpa [toSignedMarginMatrix, eps] using
      M.base.upgrade_nonneg_of_entry_nonneg M.matching hentry
  eps_ge_neg_one_of_delta_one := by
    intro i k _hdelta
    simpa [toSignedMarginMatrix, eps] using
      M.base.upgrade_ge_neg_one M.matching i k

end MatchedPMOneMatrix

def MarginTransportQge2PlanGoal : Prop :=
  ∀ {d m q r : Nat},
    Odd d → 5 ≤ d → Odd m →
    m = (d - 1) * q + r →
    r < d - 1 → 0 < r → 2 ≤ q →
    ∃ P : MarginPlan d m q r,
      Qge2PlanBounds P ∧ Nonempty (SignedMarginMatrix d P.sigma)

def MarginPlanQge2Goal : Prop :=
  ∀ {d m q r : Nat},
    Odd d → 5 ≤ d → Odd m →
    m = (d - 1) * q + r →
    r < d - 1 → 0 < r → 2 ≤ q →
    ∃ P : MarginPlan d m q r,
      Qge2PlanBounds P

def SignedMarginMatrixForQge2PlanGoal : Prop :=
  ∀ {d m q r : Nat} {P : MarginPlan d m q r},
    Odd d → 5 ≤ d → Odd m →
    m = (d - 1) * q + r →
    r < d - 1 → 0 < r → 2 ≤ q →
    Qge2PlanBounds P →
    Nonempty (SignedMarginMatrix d P.sigma)

def MarginTransportQge2Goal : Prop :=
  ∀ {d m q r : Nat},
    Odd d → 5 ≤ d → Odd m →
    m = (d - 1) * q + r →
    r < d - 1 → 0 < r → 2 ≤ q →
    ∃ P : MarginPlan d m q r,
      ∃ E : SignedMarginMatrix d P.sigma,
        ∀ i k, 0 ≤ (q : Int) - P.tau i + E.eps i k

def MarginTransportQge2CompatibleGoal : Prop :=
  ∀ {d m q r : Nat},
    Odd d → 5 ≤ d → Odd m →
    m = (d - 1) * q + r →
    r < d - 1 → 0 < r → 2 ≤ q →
    ∃ P : MarginPlan d m q r,
      ∃ E : SignedMarginMatrix d P.sigma,
        StepNonnegCompatibility P E

def MarginTransportQeq1Goal : Prop :=
  ∀ {d m q r : Nat},
    Odd d → 5 ≤ d → Odd m →
    m = (d - 1) * q + r →
    r < d - 1 → 0 < r → q = 1 →
    ∃ P : MarginPlan d m q r,
      ∃ E : SignedMarginMatrix d P.sigma,
        ∀ i k, 0 ≤ (q : Int) - P.tau i + E.eps i k

def MarginTransportQeq1CompatibleGoal : Prop :=
  ∀ {d m q r : Nat},
    Odd d → 5 ≤ d → Odd m →
    m = (d - 1) * q + r →
    r < d - 1 → 0 < r → q = 1 →
    ∃ P : MarginPlan d m q r,
      ∃ E : SignedMarginMatrix d P.sigma,
        StepNonnegCompatibility P E

def MarginTransportQeq1MatchedPMOneGoal : Prop :=
  ∀ {d m q r : Nat},
    Odd d → 5 ≤ d → Odd m →
    m = (d - 1) * q + r →
    r < d - 1 → 0 < r → q = 1 →
    ∃ P : MarginPlan d m q r,
      ∃ M : MatchedPMOneMatrix d P.sigma,
        ∀ i k, (q : Int) - P.tau i = 0 → 0 ≤ M.base.entry i k

def MarginTransportQeq1PlusFamilyGoal : Prop :=
  ∀ {d m q r : Nat},
    (hdodd : Odd d) → 5 ≤ d → Odd m →
    m = (d - 1) * q + r →
    r < d - 1 → 0 < r → q = 1 →
    ∃ P : MarginPlan d m q r,
      ∃ F : PMOneBase.PlusFamily d,
        (∀ i : Fin d,
          (∑ k : Fin (d - 2),
            (F.toBase hdodd).upgrade (F.toMatching hdodd) i k)
              = P.sigma i)
        ∧
        ∀ i k, (q : Int) - P.tau i = 0 →
          0 ≤ (F.toBase hdodd).entry i k

theorem not_marginTransportQeq1PlusFamilyGoal :
    ¬ MarginTransportQeq1PlusFamilyGoal := by
  classical
  intro hGoal
  have hdodd : Odd 5 := by norm_num
  rcases hGoal (d := 5) (m := 5) (q := 1) (r := 1)
      hdodd (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) rfl with
    ⟨P, F, hrow, _hZeroRows⟩
  have hsigma_lower : ∀ i : Fin 5, (-3 : Int) ≤ P.sigma i := by
    intro i
    have hform := F.upgraded_row_sum hdodd i
    rw [hrow i] at hform
    have hplus_nonneg : 0 ≤ 2 * ((F.rowPlusSet i).card : Int) := by
      positivity
    have hmate_nonneg : 0 ≤ ((F.rowMateSet i).card : Int) := by
      positivity
    norm_num at hform
    linarith
  have htau_nonneg : ∀ i : Fin 5, 0 ≤ P.tau i := by
    intro i
    by_contra hneg
    have htaule : P.tau i ≤ (-1 : Int) := by omega
    have hsig := hsigma_lower i
    have hdef := P.sigma_def i
    norm_num at hdef
    have hzero_le : ((P.zero i : Nat) : Int) ≤ 0 := by
      linarith
    have hzero_eq : P.zero i = 0 := by
      omega
    have hcop := P.prim_zero i
    rw [hzero_eq] at hcop
    norm_num at hcop
  have htau_zero : ∀ i : Fin 5, P.tau i = 0 := by
    have hsum : (∑ i : Fin 5, P.tau i) = 0 := by
      simpa using P.tau_sum
    have hall :
        ∀ i ∈ (Finset.univ : Finset (Fin 5)), P.tau i = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset (Fin 5)))
        (f := fun i : Fin 5 => P.tau i)
        (by
          intro i _hi
          exact htau_nonneg i)).mp hsum
    intro i
    exact hall i (by simp)
  have hsigma_nonpos : ∀ i : Fin 5, P.sigma i ≤ 0 := by
    intro i
    have hzero_ne : P.zero i ≠ 0 := by
      intro hzero
      have hcop := P.prim_zero i
      rw [hzero] at hcop
      norm_num at hcop
    have hzero_pos : 1 ≤ P.zero i := Nat.pos_of_ne_zero hzero_ne
    have hdef := P.sigma_def i
    rw [htau_zero i] at hdef
    norm_num at hdef
    linarith
  have hsigma_sum : (∑ i : Fin 5, P.sigma i) = 0 := by
    calc
      (∑ i : Fin 5, P.sigma i)
          = ∑ i : Fin 5,
              ∑ k : Fin (5 - 2),
                (F.toBase hdodd).upgrade (F.toMatching hdodd) i k := by
              apply Finset.sum_congr rfl
              intro i _hi
              exact (hrow i).symm
      _ = ∑ k : Fin (5 - 2),
              ∑ i : Fin 5,
                (F.toBase hdodd).upgrade (F.toMatching hdodd) i k := by
              rw [Finset.sum_comm]
      _ = 0 := by
              simp [(F.toBase hdodd).upgrade_col_sum_zero (F.toMatching hdodd)]
  have hsigma_zero : ∀ i : Fin 5, P.sigma i = 0 := by
    have hsum_neg : (∑ i : Fin 5, -P.sigma i) = 0 := by
      rw [Finset.sum_neg_distrib, hsigma_sum]
      simp
    have hall :
        ∀ i ∈ (Finset.univ : Finset (Fin 5)), -P.sigma i = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset (Fin 5)))
        (f := fun i : Fin 5 => -P.sigma i)
        (by
          intro i _hi
          have h := hsigma_nonpos i
          linarith)).mp hsum_neg
    intro i
    have h := hall i (by simp)
    linarith
  exact F.not_all_upgraded_row_sum_zero hdodd (by norm_num) (by
    intro i
    rw [hrow i, hsigma_zero i])

theorem marginTransportQge2Goal_of_plan
    (hPlan : MarginTransportQge2PlanGoal) :
    MarginTransportQge2Goal := by
  intro d m q r hdodd hd5 hmodd hmqr hrlt hrpos hq
  rcases hPlan hdodd hd5 hmodd hmqr hrlt hrpos hq with
    ⟨P, hP, ⟨E⟩⟩
  exact ⟨P, E, hP.step_nonneg⟩

theorem marginTransportQge2PlanGoal_of_plan_and_matrix
    (hPlan : MarginPlanQge2Goal)
    (hMatrix : SignedMarginMatrixForQge2PlanGoal) :
    MarginTransportQge2PlanGoal := by
  intro d m q r hdodd hd5 hmodd hmqr hrlt hrpos hq
  rcases hPlan hdodd hd5 hmodd hmqr hrlt hrpos hq with ⟨P, hP⟩
  exact ⟨P, hP, hMatrix hdodd hd5 hmodd hmqr hrlt hrpos hq hP⟩

theorem marginTransportQge2Goal_of_compatible
    (hCompatGoal : MarginTransportQge2CompatibleGoal) :
    MarginTransportQge2Goal := by
  intro d m q r hdodd hd5 hmodd hmqr hrlt hrpos hq
  rcases hCompatGoal hdodd hd5 hmodd hmqr hrlt hrpos hq with
    ⟨P, E, hCompat⟩
  exact ⟨P, E, hCompat.step_nonneg⟩

theorem marginTransportQge2CompatibleGoal_of_margin
    (hMargin : MarginTransportQge2Goal) :
    MarginTransportQge2CompatibleGoal := by
  intro d m q r hdodd hd5 hmodd hmqr hrlt hrpos hq
  rcases hMargin hdodd hd5 hmodd hmqr hrlt hrpos hq with
    ⟨P, E, hstep⟩
  exact ⟨P, E, StepNonnegCompatibility.of_step_nonneg hstep⟩

theorem marginTransportQeq1Goal_of_compatible
    (hCompatGoal : MarginTransportQeq1CompatibleGoal) :
    MarginTransportQeq1Goal := by
  intro d m q r hdodd hd5 hmodd hmqr hrlt hrpos hq
  rcases hCompatGoal hdodd hd5 hmodd hmqr hrlt hrpos hq with
    ⟨P, E, hCompat⟩
  exact ⟨P, E, hCompat.step_nonneg⟩

theorem marginTransportQeq1CompatibleGoal_of_margin
    (hMargin : MarginTransportQeq1Goal) :
    MarginTransportQeq1CompatibleGoal := by
  intro d m q r hdodd hd5 hmodd hmqr hrlt hrpos hq
  rcases hMargin hdodd hd5 hmodd hmqr hrlt hrpos hq with
    ⟨P, E, hstep⟩
  exact ⟨P, E, StepNonnegCompatibility.of_step_nonneg hstep⟩

theorem marginTransportQeq1CompatibleGoal_of_matchedPMOne
    (hMatched : MarginTransportQeq1MatchedPMOneGoal) :
    MarginTransportQeq1CompatibleGoal := by
  intro d m q r hdodd hd5 hmodd hmqr hrlt hrpos hq
  rcases hMatched hdodd hd5 hmodd hmqr hrlt hrpos hq with
    ⟨P, M, hZeroRows⟩
  exact ⟨P, M.toSignedMarginMatrix, M.stepNonnegCompatibility hZeroRows⟩

theorem marginTransportQeq1MatchedPMOneGoal_of_plusFamily
    (hPlus : MarginTransportQeq1PlusFamilyGoal) :
    MarginTransportQeq1MatchedPMOneGoal := by
  intro d m q r hdodd hd5 hmodd hmqr hrlt hrpos hq
  rcases hPlus hdodd hd5 hmodd hmqr hrlt hrpos hq with
    ⟨P, F, hrow, hZeroRows⟩
  refine ⟨P, ?_, ?_⟩
  · exact {
      base := F.toBase hdodd
      matching := F.toMatching hdodd
      row_sum := hrow
    }
  · exact hZeroRows

theorem transportQge2Goal_of_margin
    (hMargin : MarginTransportQge2Goal) :
    TransportQge2Goal := by
  intro d m q r hdodd hd5 hmodd hmqr hrlt hrpos hq
  rcases hMargin hdodd hd5 hmodd hmqr hrlt hrpos hq with
    ⟨P, E, hstep⟩
  exact ⟨P.toTransport E hstep⟩

theorem transportQeq1Goal_of_margin
    (hMargin : MarginTransportQeq1Goal) :
    TransportQeq1Goal := by
  intro d m q r hdodd hd5 hmodd hmqr hrlt hrpos hq
  rcases hMargin hdodd hd5 hmodd hmqr hrlt hrpos hq with
    ⟨P, E, hstep⟩
  exact ⟨P.toTransport E hstep⟩

theorem admissiblePartsCountBranchGoal_of_margin
    (hQge2 : MarginTransportQge2Goal)
    (hQeq1 : MarginTransportQeq1Goal) :
    AdmissiblePartsCountBranchGoal :=
  admissiblePartsCountBranchGoal_of_transports
    (transportQge2Goal_of_margin hQge2)
    (transportQeq1Goal_of_margin hQeq1)

end PrefixCount
end RoundComposite
