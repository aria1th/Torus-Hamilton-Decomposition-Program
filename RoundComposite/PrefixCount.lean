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
The ordinary `q >= 2` signed-core data from the v4 prefix-count proof.

Here `n` is the number of non-final rows, so the count matrix has dimension
`n + 1`; the final row carries `m - C` in the zero column and the compensating
column sums `c`.
-/
structure OrdinaryQge2SignedCoreData (n m q r : Nat) where
  C : Nat
  a : Fin n → Nat
  epsBit : Fin n → Nat
  c : Fin (n - 1) → Nat
  S : Fin n → Fin (n - 1) → Int
  C_le_m : C ≤ m
  a_sum : (∑ i : Fin n, a i) = C
  eps_sum : (∑ i : Fin n, epsBit i) = r
  c_sum : (∑ k : Fin (n - 1), c k) = C
  a_one_two : ∀ i : Fin n, a i = 1 ∨ a i = 2
  eps_zero_one : ∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1
  c_one_two : ∀ k : Fin (n - 1), c k = 1 ∨ c k = 2
  final_zero_coprime : Nat.Coprime (m - C) m
  S_signed : ∀ i k, IsSignedVal (S i k)
  S_row_sum :
    ∀ i : Fin n,
      (∑ k : Fin (n - 1), S i k)
        = (r : Int) - (a i : Int) - (n : Int) * (epsBit i : Int)
  S_col_sum :
    ∀ k : Fin (n - 1),
      (∑ i : Fin n, S i k) = - (c k : Int)

namespace OrdinaryQge2SignedCoreData

theorem a_coprime {n m q r : Nat} (D : OrdinaryQge2SignedCoreData n m q r)
    (hmodd : Odd m) (i : Fin n) :
    Nat.Coprime (D.a i) m := by
  rcases D.a_one_two i with h | h
  · simp [h]
  · simpa [h] using hmodd.coprime_two_left

theorem c_signed {n m q r : Nat} (D : OrdinaryQge2SignedCoreData n m q r)
    (k : Fin (n - 1)) :
    IsSignedVal (D.c k : Int) := by
  rcases D.c_one_two k with h | h <;> simp [h, IsSignedVal, signedVals]

theorem c_nonneg {n m q r : Nat} (D : OrdinaryQge2SignedCoreData n m q r)
    (k : Fin (n - 1)) :
    0 ≤ (D.c k : Int) := by
  rcases D.c_one_two k with h | h <;> simp [h]

theorem sum_a_add_final_zero {n m q r : Nat}
    (D : OrdinaryQge2SignedCoreData n m q r) :
    (∑ i : Fin (n + 1),
        Fin.lastCases (m - D.C) D.a i) = m := by
  rw [Fin.sum_univ_castSucc]
  simp [D.a_sum]
  have hC := D.C_le_m
  omega

theorem sum_c_int {n m q r : Nat}
    (D : OrdinaryQge2SignedCoreData n m q r) :
    (∑ k : Fin (n - 1), (D.c k : Int)) = (D.C : Int) := by
  exact_mod_cast D.c_sum

theorem sum_eps_int {n m q r : Nat}
    (D : OrdinaryQge2SignedCoreData n m q r) :
    (∑ i : Fin n, (D.epsBit i : Int)) = (r : Int) := by
  exact_mod_cast D.eps_sum

theorem marginTransportQge2Compatible_of_ordinaryData
    {n m q r : Nat} (hmodd : Odd m) (hmqr : m = n * q + r)
    (hq : 2 ≤ q)
    (D : OrdinaryQge2SignedCoreData n m q r) :
    ∃ P : MarginPlan (n + 1) m q r,
      ∃ E : SignedMarginMatrix (n + 1) P.sigma,
        StepNonnegCompatibility P E := by
  classical
  let zero : Fin (n + 1) → Nat := Fin.lastCases (m - D.C) D.a
  let tau : Fin (n + 1) → Int :=
    Fin.lastCases (q : Int) (fun i : Fin n => - (D.epsBit i : Int))
  let sigma : Fin (n + 1) → Int :=
    Fin.lastCases (D.C : Int)
      (fun i : Fin n =>
        (r : Int) - (D.a i : Int) - (n : Int) * (D.epsBit i : Int))
  let P : MarginPlan (n + 1) m q r := {
    zero := zero
    tau := tau
    sigma := sigma
    sigma_def := by
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simp [zero, tau, sigma]
        ring
      · simp only [zero, tau, sigma, Fin.lastCases_last, add_tsub_cancel_right]
        have hmqrInt : (m : Int) = (n : Int) * (q : Int) + (r : Int) := by
          rw [hmqr]
          norm_num [Nat.cast_add, Nat.cast_mul]
        have hsub : ((m - D.C : Nat) : Int) = (m : Int) - (D.C : Int) := by
          have hC := D.C_le_m
          omega
        rw [hsub, hmqrInt]
        ring
    tau_sum := by
      rw [Fin.sum_univ_castSucc]
      simp [tau, D.sum_eps_int]
      ring
    delta_nonneg := by
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · have heps : 0 ≤ (D.epsBit j : Int) := by omega
        simp [tau]
        omega
      · simp [tau]
    prim_zero := by
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simpa [zero] using D.a_coprime hmodd j
      · simpa [zero] using D.final_zero_coprime
  }
  let E : SignedMarginMatrix (n + 1) P.sigma := {
    eps := Fin.lastCases (fun k : Fin (n - 1) => (D.c k : Int)) D.S
    eps_signed := by
      intro i k
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simpa using D.S_signed j k
      · simpa using D.c_signed k
    row_sum := by
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simpa [sigma, P] using D.S_row_sum j
      · simpa [sigma, P] using D.sum_c_int
    col_sum := by
      intro k
      rw [Fin.sum_univ_castSucc]
      simp [D.S_col_sum k]
  }
  refine ⟨P, E, StepNonnegCompatibility.of_step_nonneg ?_⟩
  intro i k
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · have hqInt : (2 : Int) ≤ (q : Int) := by exact_mod_cast hq
    have hepsLower := signedVal_ge_neg_two (D.S_signed j k)
    have hepsBit : 0 ≤ (D.epsBit j : Int) := by omega
    simp [P, tau, E]
    linarith
  · simp [P, tau, E, D.c_nonneg k]

end OrdinaryQge2SignedCoreData

/-- The easy row/column seed choices for the ordinary `q >= 2` branch, before
the signed-column closure produces the actual signed matrix. -/
structure OrdinaryQge2PlanData (n m q r : Nat) where
  C : Nat
  a : Fin n → Nat
  epsBit : Fin n → Nat
  c : Fin (n - 1) → Nat
  C_le_m : C ≤ m
  a_sum : (∑ i : Fin n, a i) = C
  eps_sum : (∑ i : Fin n, epsBit i) = r
  c_sum : (∑ k : Fin (n - 1), c k) = C
  a_one_two : ∀ i : Fin n, a i = 1 ∨ a i = 2
  eps_zero_one : ∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1
  c_one_two : ∀ k : Fin (n - 1), c k = 1 ∨ c k = 2
  final_zero_coprime : Nat.Coprime (m - C) m

namespace OrdinaryQge2PlanData

/-- The hard signed-column output for a fixed ordinary `q >= 2` plan. -/
structure SignedMatrixData {n m q r : Nat}
    (P : OrdinaryQge2PlanData n m q r) where
  S : Fin n → Fin (n - 1) → Int
  S_signed : ∀ i k, IsSignedVal (S i k)
  S_row_sum :
    ∀ i : Fin n,
      (∑ k : Fin (n - 1), S i k)
        = (r : Int) - (P.a i : Int) - (n : Int) * (P.epsBit i : Int)
  S_col_sum :
    ∀ k : Fin (n - 1),
      (∑ i : Fin n, S i k) = - (P.c k : Int)

def toCoreData {n m q r : Nat} (P : OrdinaryQge2PlanData n m q r)
    (S : P.SignedMatrixData) :
    OrdinaryQge2SignedCoreData n m q r where
  C := P.C
  a := P.a
  epsBit := P.epsBit
  c := P.c
  S := S.S
  C_le_m := P.C_le_m
  a_sum := P.a_sum
  eps_sum := P.eps_sum
  c_sum := P.c_sum
  a_one_two := P.a_one_two
  eps_zero_one := P.eps_zero_one
  c_one_two := P.c_one_two
  final_zero_coprime := P.final_zero_coprime
  S_signed := S.S_signed
  S_row_sum := S.S_row_sum
  S_col_sum := S.S_col_sum

end OrdinaryQge2PlanData

/--
Paper-facing ordinary signed-core theorem for the `q >= 2` branch.

The parameter `n` is `d - 1`; this keeps the distinguished final row
definitionally visible as the last row of `Fin (n + 1)`.
-/
def OrdinaryQge2SignedCoreGoal : Prop :=
  ∀ {n m q r : Nat},
    Odd (n + 1) → 5 ≤ n + 1 → Odd m →
    m = n * q + r →
    r < n → 0 < r → 2 ≤ q →
    Nonempty (OrdinaryQge2SignedCoreData n m q r)

theorem sum_fin_indicator_val_lt (n k : Nat) :
    (∑ i : Fin n, if i.val < k then (1 : Nat) else 0) = min n k := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j => if j < k then (1 : Nat) else 0) n]
  rw [← Finset.card_filter]
  have h :
      (Finset.range n).filter (fun i => i < k) =
        Finset.range (min n k) := by
    ext i
    simp
  rw [h]
  simp

theorem sum_fin_two_one_val_lt (n k : Nat) :
    (∑ i : Fin n, if i.val < k then (2 : Nat) else 1) =
      n + min n k := by
  calc
    (∑ i : Fin n, if i.val < k then (2 : Nat) else 1)
        = ∑ i : Fin n, (1 + if i.val < k then (1 : Nat) else 0) := by
          apply Finset.sum_congr rfl
          intro i _hi
          by_cases h : i.val < k <;> simp [h]
    _ = (∑ _i : Fin n, (1 : Nat))
          + ∑ i : Fin n, (if i.val < k then (1 : Nat) else 0) := by
          rw [Finset.sum_add_distrib]
    _ = n + min n k := by
          rw [sum_fin_indicator_val_lt]
          simp

def OrdinaryQge2PlanGoal : Prop :=
  ∀ {n m q r : Nat},
    Odd (n + 1) → 5 ≤ n + 1 → Odd m →
    m = n * q + r →
    r < n → 0 < r → 2 ≤ q →
    Nonempty (OrdinaryQge2PlanData n m q r)

def OrdinaryQge2SeedGoal : Prop :=
  ∀ {n m q r : Nat},
    Odd (n + 1) → 5 ≤ n + 1 → Odd m →
    m = n * q + r →
    r < n → 0 < r → 2 ≤ q →
    ∃ C : Nat,
      n ≤ C ∧ C ≤ 2 * (n - 1) ∧ C ≤ m ∧ Nat.Coprime (m - C) m

theorem ordinaryQge2PlanGoal_of_seed
    (hSeed : OrdinaryQge2SeedGoal) :
    OrdinaryQge2PlanGoal := by
  intro n m q r hdodd hd5 hmodd hmqr hrlt hrpos hq
  rcases hSeed hdodd hd5 hmodd hmqr hrlt hrpos hq with
    ⟨C, hCn, hC2, hCm, hCcop⟩
  refine ⟨{
    C := C
    a := fun i : Fin n => if i.val < C - n then 2 else 1
    epsBit := fun i : Fin n => if i.val < r then 1 else 0
    c := fun k : Fin (n - 1) => if k.val < C - (n - 1) then 2 else 1
    C_le_m := hCm
    a_sum := ?_
    eps_sum := ?_
    c_sum := ?_
    a_one_two := ?_
    eps_zero_one := ?_
    c_one_two := ?_
    final_zero_coprime := hCcop
  }⟩
  · rw [sum_fin_two_one_val_lt]
    have hmin : min n (C - n) = C - n := by omega
    rw [hmin]
    omega
  · rw [sum_fin_indicator_val_lt]
    have hmin : min n r = r := by omega
    exact hmin
  · rw [sum_fin_two_one_val_lt]
    have hmin : min (n - 1) (C - (n - 1)) = C - (n - 1) := by
      omega
    rw [hmin]
    omega
  · intro i
    by_cases h : i.val < C - n <;> simp [h]
  · intro i
    by_cases h : i.val < r <;> simp [h]
  · intro k
    by_cases h : k.val < C - (n - 1) <;> simp [h]

theorem ordinaryQge2SeedGoal : OrdinaryQge2SeedGoal := by
  intro n m q r hdodd hd5 hmodd hmqr hrlt hrpos hq
  have hn1 : 1 ≤ n := by omega
  have hn4 : 4 ≤ n := by omega
  rcases exists_power_two_ge_self_lt_two_mul (L := n) hn1 with
    ⟨e, hCn, hClt⟩
  have hC2 : 2 ^ e ≤ 2 * (n - 1) := by
    have hEvenC : ∃ k, 2 ^ e = 2 * k := by
      cases e with
      | zero =>
          simp at hCn
          omega
      | succ e =>
          refine ⟨2 ^ e, ?_⟩
          rw [pow_succ]
          ring
    rcases hEvenC with ⟨k, hk⟩
    omega
  have hCle : 2 ^ e ≤ m := by
    have hnq : n * 2 ≤ n * q := Nat.mul_le_mul_left n hq
    have htwonm1 : 2 * (n - 1) ≤ m := by
      omega
    exact le_trans hC2 htwonm1
  refine ⟨2 ^ e, hCn, hC2, hCle, ?_⟩
  have hepos : 0 < e := by
    cases e with
    | zero =>
        simp at hCn
        omega
    | succ e => exact Nat.succ_pos e
  have hCcop : Nat.Coprime (2 ^ e) m := by
    rw [Nat.coprime_pow_left_iff hepos]
    exact Nat.coprime_two_left.mpr hmodd
  exact (Nat.coprime_self_sub_left hCle).2 hCcop

theorem ordinaryQge2PlanGoal : OrdinaryQge2PlanGoal :=
  ordinaryQge2PlanGoal_of_seed ordinaryQge2SeedGoal

def qge2ColumnCapacity (n j c : Nat) : Int :=
  min (2 * (j : Int)) (2 * ((n - j : Nat) : Int) - (c : Int))

theorem qge2ColumnCapacity_eq_left {n j c : Nat}
    (h : 2 * (j : Int) ≤ 2 * ((n - j : Nat) : Int) - (c : Int)) :
    qge2ColumnCapacity n j c = 2 * (j : Int) := by
  simp [qge2ColumnCapacity, min_eq_left h]

theorem qge2ColumnCapacity_eq_right {n j c : Nat}
    (h : 2 * ((n - j : Nat) : Int) - (c : Int) ≤ 2 * (j : Int)) :
    qge2ColumnCapacity n j c = 2 * ((n - j : Nat) : Int) - (c : Int) := by
  simp [qge2ColumnCapacity, min_eq_right h]

theorem ordinaryQge2PlanData_row_cut_first_bound
    {n m q r : Nat} (P : OrdinaryQge2PlanData n m q r)
    (J : Finset (Fin n)) :
    (∑ i ∈ J, ((r : Int) - (P.a i : Int)
        - (n : Int) * (P.epsBit i : Int)))
      ≤ (J.card : Int) * ((r : Int) - 1) := by
  classical
  calc
    (∑ i ∈ J, ((r : Int) - (P.a i : Int)
        - (n : Int) * (P.epsBit i : Int)))
        ≤ ∑ _i ∈ J, ((r : Int) - 1) := by
          apply Finset.sum_le_sum
          intro i _hi
          have ha : 1 ≤ (P.a i : Int) := by
            rcases P.a_one_two i with h | h <;> simp [h]
          have heps : 0 ≤ (P.epsBit i : Int) := by omega
          have hn : 0 ≤ (n : Int) := by omega
          nlinarith
    _ = (J.card : Int) * ((r : Int) - 1) := by
          simp [Finset.sum_const, mul_comm]
          ring

theorem ordinaryQge2PlanData_row_cut_second_bound
    {n m q r : Nat} (P : OrdinaryQge2PlanData n m q r)
    (J : Finset (Fin n)) :
    (∑ i ∈ J, ((r : Int) - (P.a i : Int)
        - (n : Int) * (P.epsBit i : Int)))
      ≤ - (P.C : Int) + ((n - J.card : Nat) : Int)
          * ((n : Int) + 2 - (r : Int)) := by
  classical
  let R : Fin n → Int :=
    fun i => (r : Int) - (P.a i : Int)
      - (n : Int) * (P.epsBit i : Int)
  have htotal : (∑ i : Fin n, R i) = - (P.C : Int) := by
    calc
      (∑ i : Fin n, R i)
          = (∑ _i : Fin n, (r : Int))
              - (∑ i : Fin n, (P.a i : Int))
              - (n : Int) * (∑ i : Fin n, (P.epsBit i : Int)) := by
                simp [R, Finset.sum_sub_distrib, Finset.mul_sum,
                  Finset.sum_const]
      _ = (n : Int) * (r : Int) - (P.C : Int)
              - (n : Int) * (r : Int) := by
                have ha : (∑ i : Fin n, (P.a i : Int)) = (P.C : Int) := by
                  exact_mod_cast P.a_sum
                have heps :
                    (∑ i : Fin n, (P.epsBit i : Int)) = (r : Int) := by
                  exact_mod_cast P.eps_sum
                rw [ha, heps]
                simp [Finset.sum_const]
      _ = - (P.C : Int) := by ring
  have hcompl_card : ((Jᶜ).card : Int) = ((n - J.card : Nat) : Int) := by
    have hcard : Jᶜ.card = n - J.card := by
      simpa [Fintype.card_fin] using Finset.card_compl J
    exact_mod_cast hcard
  have hcompl_lower :
      ((Jᶜ).card : Int) * ((r : Int) - (n : Int) - 2)
        ≤ ∑ i ∈ Jᶜ, R i := by
    calc
      ((Jᶜ).card : Int) * ((r : Int) - (n : Int) - 2)
          = ∑ _i ∈ Jᶜ, ((r : Int) - (n : Int) - 2) := by
              simp [Finset.sum_const, mul_comm]
              ring
      _ ≤ ∑ i ∈ Jᶜ, R i := by
              apply Finset.sum_le_sum
              intro i _hi
              have ha : (P.a i : Int) ≤ 2 := by
                rcases P.a_one_two i with h | h <;> simp [h]
              have heps : (P.epsBit i : Int) ≤ 1 := by
                rcases P.eps_zero_one i with h | h <;> simp [h]
              have hn : 0 ≤ (n : Int) := by omega
              simp [R]
              nlinarith
  have hsplit :
      (∑ i : Fin n, R i) = (∑ i ∈ J, R i) + ∑ i ∈ Jᶜ, R i := by
    rw [← Finset.sum_union]
    · simp
    · exact disjoint_compl_right
  have hJ :
      (∑ i ∈ J, R i)
        ≤ - (P.C : Int)
            - ((Jᶜ).card : Int) * ((r : Int) - (n : Int) - 2) := by
    rw [hsplit] at htotal
    nlinarith
  calc
    (∑ i ∈ J, ((r : Int) - (P.a i : Int)
        - (n : Int) * (P.epsBit i : Int)))
        = ∑ i ∈ J, R i := rfl
    _ ≤ - (P.C : Int)
            - ((Jᶜ).card : Int) * ((r : Int) - (n : Int) - 2) := hJ
    _ = - (P.C : Int) + ((n - J.card : Nat) : Int)
          * ((n : Int) + 2 - (r : Int)) := by
            rw [hcompl_card]
            ring

theorem ordinaryQge2PlanData_column_capacity_low
    {n m q r : Nat} (P : OrdinaryQge2PlanData n m q r)
    {j : Nat} (hn1 : 1 ≤ n) (hj : 2 * j ≤ n - 1) :
    (∑ k : Fin (n - 1), qge2ColumnCapacity n j (P.c k))
      = ((n - 1 : Nat) : Int) * (2 * (j : Int)) := by
  classical
  calc
    (∑ k : Fin (n - 1), qge2ColumnCapacity n j (P.c k))
        = ∑ _k : Fin (n - 1), 2 * (j : Int) := by
            apply Finset.sum_congr rfl
            intro k _hk
            apply qge2ColumnCapacity_eq_left
            have hjIntNat : ((2 * j : Nat) : Int) ≤ ((n - 1 : Nat) : Int) := by
              exact_mod_cast hj
            have hjInt : 2 * (j : Int) ≤ (n : Int) - 1 := by
              have hpred : ((n - 1 : Nat) : Int) = (n : Int) - 1 := by
                omega
              rw [← hpred]
              exact hjIntNat
            have hjn : j ≤ n := by omega
            have hsub : ((n - j : Nat) : Int) = (n : Int) - (j : Int) := by
              omega
            rw [hsub]
            rcases P.c_one_two k with hc | hc <;> simp [hc] <;> omega
    _ = ((n - 1 : Nat) : Int) * (2 * (j : Int)) := by
          simp [Finset.sum_const]

theorem ordinaryQge2PlanData_column_capacity_high
    {n m q r : Nat} (P : OrdinaryQge2PlanData n m q r)
    {j : Nat} (hj : n ≤ 2 * j) :
    (∑ k : Fin (n - 1), qge2ColumnCapacity n j (P.c k))
      =
      ((n - 1 : Nat) : Int) * (2 * ((n - j : Nat) : Int))
        - (P.C : Int) := by
  classical
  calc
    (∑ k : Fin (n - 1), qge2ColumnCapacity n j (P.c k))
        = ∑ k : Fin (n - 1),
            (2 * ((n - j : Nat) : Int) - (P.c k : Int)) := by
              apply Finset.sum_congr rfl
              intro k _hk
              apply qge2ColumnCapacity_eq_right
              have hc : 1 ≤ (P.c k : Int) := by
                rcases P.c_one_two k with h | h <;> simp [h]
              have hjn : j ≤ n ∨ n ≤ j := by omega
              have hsub_nonneg : 0 ≤ ((n - j : Nat) : Int) := by omega
              have hsub_le : ((n - j : Nat) : Int) ≤ (j : Int) := by
                omega
              nlinarith
    _ = (∑ _k : Fin (n - 1), 2 * ((n - j : Nat) : Int))
          - ∑ k : Fin (n - 1), (P.c k : Int) := by
            rw [Finset.sum_sub_distrib]
    _ =
      ((n - 1 : Nat) : Int) * (2 * ((n - j : Nat) : Int))
        - (P.C : Int) := by
          have hc_sum : (∑ k : Fin (n - 1), (P.c k : Int)) = (P.C : Int) := by
            exact_mod_cast P.c_sum
          rw [hc_sum]
          simp [Finset.sum_const]

theorem ordinaryQge2PlanData_row_cut_capacity
    {n m q r : Nat}
    (_hdodd : Odd (n + 1)) (hd5 : 5 ≤ n + 1)
    (hrlt : r < n)
    (P : OrdinaryQge2PlanData n m q r)
    (J : Finset (Fin n)) :
    (∑ i ∈ J, ((r : Int) - (P.a i : Int)
        - (n : Int) * (P.epsBit i : Int)))
      ≤ ∑ k : Fin (n - 1), qge2ColumnCapacity n J.card (P.c k) := by
  classical
  have hn4 : 4 ≤ n := by omega
  by_cases hjlow : 2 * J.card ≤ n - 1
  · rw [ordinaryQge2PlanData_column_capacity_low P (by omega) hjlow]
    have hfirst := ordinaryQge2PlanData_row_cut_first_bound P J
    have hcard_nonneg : 0 ≤ (J.card : Int) := by omega
    have hrle : (r : Int) - 1 ≤ 2 * ((n - 1 : Nat) : Int) := by omega
    nlinarith
  · have hjhigh : n ≤ 2 * J.card := by omega
    rw [ordinaryQge2PlanData_column_capacity_high P hjhigh]
    have hsecond := ordinaryQge2PlanData_row_cut_second_bound P J
    have hcardle : J.card ≤ n := by
      simpa using Finset.card_le_univ J
    have hnonneg : 0 ≤ ((n - J.card : Nat) : Int) := by omega
    have hfactor :
        (n : Int) + 2 - (r : Int)
          ≤ 2 * ((n - 1 : Nat) : Int) := by omega
    nlinarith

/--
The exact external signed-column closure input used by the ordinary `q >= 2`
branch.  The preceding Lean lemmas prove the row-cut side condition for the
canonical ordinary plans; this goal is only the integral Hoffman/Rado-Edmonds
decomposition of those cuts into columns with entries in `{±1, ±2}`.
-/
def OrdinaryQge2SignedSeedClosureGoal : Prop :=
  ∀ {n C r : Nat},
    Even n → 4 ≤ n → Odd r → r < n → 0 < r →
    ∀ (a : Fin n → Nat) (epsBit : Fin n → Nat) (c : Fin (n - 1) → Nat),
      (∀ i : Fin n, a i = 1 ∨ a i = 2) →
      (∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1) →
      (∀ k : Fin (n - 1), c k = 1 ∨ c k = 2) →
      (∑ i : Fin n, a i) = C →
      (∑ i : Fin n, epsBit i) = r →
      (∑ k : Fin (n - 1), c k) = C →
      (∀ J : Finset (Fin n),
        (∑ i ∈ J, ((r : Int) - (a i : Int)
            - (n : Int) * (epsBit i : Int)))
          ≤ ∑ k : Fin (n - 1), qge2ColumnCapacity n J.card (c k)) →
      ∃ S : Fin n → Fin (n - 1) → Int,
        (∀ i k, IsSignedVal (S i k)) ∧
        (∀ i : Fin n,
          (∑ k : Fin (n - 1), S i k)
            = (r : Int) - (a i : Int) - (n : Int) * (epsBit i : Int)) ∧
        (∀ k : Fin (n - 1), (∑ i : Fin n, S i k) = - (c k : Int))

def OrdinaryQge2SignedMatrixGoal : Prop :=
  ∀ {n m q r : Nat},
    Odd (n + 1) → 5 ≤ n + 1 → Odd m →
    m = n * q + r →
    r < n → 0 < r → 2 ≤ q →
    ∀ P : OrdinaryQge2PlanData n m q r,
      Nonempty P.SignedMatrixData

theorem ordinaryQge2SignedMatrixGoal_of_signedSeedClosure
    (hClosure : OrdinaryQge2SignedSeedClosureGoal) :
    OrdinaryQge2SignedMatrixGoal := by
  intro n m q r hdodd hd5 hmodd hmqr hrlt hrpos _hq P
  have hnEven : Even n := by
    rcases hdodd with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hrodd : Odd r := by
    by_contra hnot
    have hre : Even r := Nat.not_odd_iff_even.mp hnot
    rcases hnEven with ⟨a, ha⟩
    rcases hre with ⟨b, hb⟩
    have hmeven : Even m := by
      refine ⟨a * q + b, ?_⟩
      rw [hmqr, ha, hb]
      ring
    exact (Nat.not_even_iff_odd.mpr hmodd) hmeven
  have hCuts :
      ∀ J : Finset (Fin n),
        (∑ i ∈ J, ((r : Int) - (P.a i : Int)
            - (n : Int) * (P.epsBit i : Int)))
          ≤ ∑ k : Fin (n - 1), qge2ColumnCapacity n J.card (P.c k) :=
    ordinaryQge2PlanData_row_cut_capacity hdodd hd5 hrlt P
  rcases hClosure hnEven (by omega) hrodd hrlt hrpos
      P.a P.epsBit P.c P.a_one_two P.eps_zero_one P.c_one_two
      P.a_sum P.eps_sum P.c_sum hCuts with
    ⟨S, hSigned, hRow, hCol⟩
  exact ⟨{
    S := S
    S_signed := hSigned
    S_row_sum := hRow
    S_col_sum := hCol
  }⟩

theorem ordinaryQge2SignedCoreGoal_of_plan_and_matrix
    (hPlan : OrdinaryQge2PlanGoal)
    (hMatrix : OrdinaryQge2SignedMatrixGoal) :
    OrdinaryQge2SignedCoreGoal := by
  intro n m q r hdodd hd5 hmodd hmqr hrlt hrpos hq
  rcases hPlan hdodd hd5 hmodd hmqr hrlt hrpos hq with ⟨P⟩
  rcases hMatrix hdodd hd5 hmodd hmqr hrlt hrpos hq P with ⟨S⟩
  exact ⟨P.toCoreData S⟩

/--
The restricted `q = 1` signed-core data from the v4 prefix-count proof.

Again `n` is the number of non-final rows.  Rows with `epsBit = 0` carry the
extra restriction that their signed entries are at least `-1`, exactly matching
the `q = 1` nonnegativity boundary.
-/
structure OrdinaryQeq1SignedCoreData (n m r : Nat) where
  a : Fin n → Nat
  epsBit : Fin n → Nat
  c : Fin (n - 1) → Nat
  S : Fin n → Fin (n - 1) → Int
  a_sum : (∑ i : Fin n, a i) = m - 1
  eps_sum : (∑ i : Fin n, epsBit i) = r
  c_sum : (∑ k : Fin (n - 1), c k) = m - 1
  a_one_two : ∀ i : Fin n, a i = 1 ∨ a i = 2
  eps_zero_one : ∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1
  c_one_two : ∀ k : Fin (n - 1), c k = 1 ∨ c k = 2
  S_signed : ∀ i k, IsSignedVal (S i k)
  S_ge_neg_one_of_eps_zero :
    ∀ i k, epsBit i = 0 → (-1 : Int) ≤ S i k
  S_row_sum :
    ∀ i : Fin n,
      (∑ k : Fin (n - 1), S i k)
        = (r : Int) - (a i : Int) - (n : Int) * (epsBit i : Int)
  S_col_sum :
    ∀ k : Fin (n - 1),
      (∑ i : Fin n, S i k) = - (c k : Int)

namespace OrdinaryQeq1SignedCoreData

theorem a_coprime {n m r : Nat} (D : OrdinaryQeq1SignedCoreData n m r)
    (hmodd : Odd m) (i : Fin n) :
    Nat.Coprime (D.a i) m := by
  rcases D.a_one_two i with h | h
  · simp [h]
  · simpa [h] using hmodd.coprime_two_left

theorem c_signed {n m r : Nat} (D : OrdinaryQeq1SignedCoreData n m r)
    (k : Fin (n - 1)) :
    IsSignedVal (D.c k : Int) := by
  rcases D.c_one_two k with h | h <;> simp [h, IsSignedVal, signedVals]

theorem c_nonneg {n m r : Nat} (D : OrdinaryQeq1SignedCoreData n m r)
    (k : Fin (n - 1)) :
    0 ≤ (D.c k : Int) := by
  rcases D.c_one_two k with h | h <;> simp [h]

theorem sum_c_int {n m r : Nat}
    (D : OrdinaryQeq1SignedCoreData n m r) :
    (∑ k : Fin (n - 1), (D.c k : Int)) = ((m - 1 : Nat) : Int) := by
  exact_mod_cast D.c_sum

theorem sum_eps_int {n m r : Nat}
    (D : OrdinaryQeq1SignedCoreData n m r) :
    (∑ i : Fin n, (D.epsBit i : Int)) = (r : Int) := by
  exact_mod_cast D.eps_sum

theorem marginTransportQeq1Compatible_of_ordinaryData
    {n m r : Nat} (hmodd : Odd m) (hmnr : m = n + r)
    (hrpos : 0 < r) (D : OrdinaryQeq1SignedCoreData n m r) :
    ∃ P : MarginPlan (n + 1) m 1 r,
      ∃ E : SignedMarginMatrix (n + 1) P.sigma,
        StepNonnegCompatibility P E := by
  classical
  have hmpos : 1 ≤ m := by omega
  let zero : Fin (n + 1) → Nat := Fin.lastCases 1 D.a
  let tau : Fin (n + 1) → Int :=
    Fin.lastCases (1 : Int) (fun i : Fin n => - (D.epsBit i : Int))
  let sigma : Fin (n + 1) → Int :=
    Fin.lastCases ((m - 1 : Nat) : Int)
      (fun i : Fin n =>
        (r : Int) - (D.a i : Int) - (n : Int) * (D.epsBit i : Int))
  let P : MarginPlan (n + 1) m 1 r := {
    zero := zero
    tau := tau
    sigma := sigma
    sigma_def := by
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simp [zero, tau, sigma]
        ring
      · simp only [zero, tau, sigma, Fin.lastCases_last, add_tsub_cancel_right]
        have hmnrInt : (m : Int) = (n : Int) + (r : Int) := by
          rw [hmnr]
          norm_num [Nat.cast_add]
        have hsub : ((m - 1 : Nat) : Int) = (m : Int) - 1 := by
          omega
        rw [hsub, hmnrInt]
        ring
    tau_sum := by
      rw [Fin.sum_univ_castSucc]
      simp [tau, D.sum_eps_int]
      ring
    delta_nonneg := by
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · have heps : 0 ≤ (D.epsBit j : Int) := by omega
        simp [tau]
        omega
      · simp [tau]
    prim_zero := by
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simpa [zero] using D.a_coprime hmodd j
      · simp [zero]
  }
  let E : SignedMarginMatrix (n + 1) P.sigma := {
    eps := Fin.lastCases (fun k : Fin (n - 1) => (D.c k : Int)) D.S
    eps_signed := by
      intro i k
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simpa using D.S_signed j k
      · simpa using D.c_signed k
    row_sum := by
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simpa [sigma, P] using D.S_row_sum j
      · simpa [sigma, P] using D.sum_c_int
    col_sum := by
      intro k
      rw [Fin.sum_univ_castSucc]
      simp [D.S_col_sum k]
  }
  refine ⟨P, E, StepNonnegCompatibility.of_step_nonneg ?_⟩
  intro i k
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rcases D.eps_zero_one j with heps | heps
    · have hS := D.S_ge_neg_one_of_eps_zero j k heps
      simp [P, tau, E, heps]
      linarith
    · have hS := signedVal_ge_neg_two (D.S_signed j k)
      simp [P, tau, E, heps]
      linarith
  · simp [P, tau, E, D.c_nonneg k]

end OrdinaryQeq1SignedCoreData

def OrdinaryQeq1SignedCoreGoal : Prop :=
  ∀ {n m r : Nat},
    Odd (n + 1) → 5 ≤ n + 1 → Odd m →
    m = n + r →
    r < n → 0 < r →
    Nonempty (OrdinaryQeq1SignedCoreData n m r)

structure OrdinaryQeq1PlanData (n m r : Nat) where
  a : Fin n → Nat
  epsBit : Fin n → Nat
  c : Fin (n - 1) → Nat
  a_sum : (∑ i : Fin n, a i) = m - 1
  eps_sum : (∑ i : Fin n, epsBit i) = r
  c_sum : (∑ k : Fin (n - 1), c k) = m - 1
  a_one_two : ∀ i : Fin n, a i = 1 ∨ a i = 2
  eps_zero_one : ∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1
  c_one_two : ∀ k : Fin (n - 1), c k = 1 ∨ c k = 2

namespace OrdinaryQeq1PlanData

structure SignedMatrixData {n m r : Nat}
    (P : OrdinaryQeq1PlanData n m r) where
  S : Fin n → Fin (n - 1) → Int
  S_signed : ∀ i k, IsSignedVal (S i k)
  S_ge_neg_one_of_eps_zero :
    ∀ i k, P.epsBit i = 0 → (-1 : Int) ≤ S i k
  S_row_sum :
    ∀ i : Fin n,
      (∑ k : Fin (n - 1), S i k)
        = (r : Int) - (P.a i : Int) - (n : Int) * (P.epsBit i : Int)
  S_col_sum :
    ∀ k : Fin (n - 1),
      (∑ i : Fin n, S i k) = - (P.c k : Int)

def toCoreData {n m r : Nat} (P : OrdinaryQeq1PlanData n m r)
    (S : P.SignedMatrixData) :
    OrdinaryQeq1SignedCoreData n m r where
  a := P.a
  epsBit := P.epsBit
  c := P.c
  S := S.S
  a_sum := P.a_sum
  eps_sum := P.eps_sum
  c_sum := P.c_sum
  a_one_two := P.a_one_two
  eps_zero_one := P.eps_zero_one
  c_one_two := P.c_one_two
  S_signed := S.S_signed
  S_ge_neg_one_of_eps_zero := S.S_ge_neg_one_of_eps_zero
  S_row_sum := S.S_row_sum
  S_col_sum := S.S_col_sum

end OrdinaryQeq1PlanData

def OrdinaryQeq1PlanGoal : Prop :=
  ∀ {n m r : Nat},
    Odd (n + 1) → 5 ≤ n + 1 → Odd m →
    m = n + r →
    r < n → 0 < r →
    Nonempty (OrdinaryQeq1PlanData n m r)

def OrdinaryQeq1SignedMatrixGoal : Prop :=
  ∀ {n m r : Nat},
    Odd (n + 1) → 5 ≤ n + 1 → Odd m →
    m = n + r →
    r < n → 0 < r →
    ∀ P : OrdinaryQeq1PlanData n m r,
      Nonempty P.SignedMatrixData

theorem ordinaryQeq1SignedCoreGoal_of_plan_and_matrix
    (hPlan : OrdinaryQeq1PlanGoal)
    (hMatrix : OrdinaryQeq1SignedMatrixGoal) :
    OrdinaryQeq1SignedCoreGoal := by
  intro n m r hdodd hd5 hmodd hmnr hrlt hrpos
  rcases hPlan hdodd hd5 hmodd hmnr hrlt hrpos with ⟨P⟩
  rcases hMatrix hdodd hd5 hmodd hmnr hrlt hrpos P with ⟨S⟩
  exact ⟨P.toCoreData S⟩

theorem ordinaryQeq1PlanGoal : OrdinaryQeq1PlanGoal := by
  intro n m r _hdodd _hd5 _hmodd hmnr hrlt hrpos
  refine ⟨{
    a := fun i : Fin n => if i.val < r - 1 then 2 else 1
    epsBit := fun i : Fin n => if i.val < r then 1 else 0
    c := fun k : Fin (n - 1) => if k.val < r then 2 else 1
    a_sum := ?_
    eps_sum := ?_
    c_sum := ?_
    a_one_two := ?_
    eps_zero_one := ?_
    c_one_two := ?_
  }⟩
  · rw [sum_fin_two_one_val_lt]
    have hmin : min n (r - 1) = r - 1 := by omega
    rw [hmin, hmnr]
    omega
  · rw [sum_fin_indicator_val_lt]
    have hmin : min n r = r := by omega
    exact hmin
  · rw [sum_fin_two_one_val_lt]
    have hmin : min (n - 1) r = r := by omega
    rw [hmin, hmnr]
    omega
  · intro i
    by_cases h : i.val < r - 1 <;> simp [h]
  · intro i
    by_cases h : i.val < r <;> simp [h]
  · intro k
    by_cases h : k.val < r <;> simp [h]

/--
Canonical signed matrix output for the manuscript's restricted `q = 1`
matching correction.  This is weaker than asking for signed matrices for every
possible `OrdinaryQeq1PlanData`; it targets the canonical plan used in v4.
-/
structure OrdinaryQeq1CanonicalMatrixData (n m r : Nat) where
  S : Fin n → Fin (n - 1) → Int
  S_signed : ∀ i k, IsSignedVal (S i k)
  S_ge_neg_one_of_P :
    ∀ i k, r ≤ i.val → (-1 : Int) ≤ S i k
  S_row_sum :
    ∀ i : Fin n,
      (∑ k : Fin (n - 1), S i k)
        =
        if i.val < r - 1 then
          (r : Int) - 2 - (n : Int)
        else if i.val < r then
          (r : Int) - 1 - (n : Int)
        else
          (r : Int) - 1
  S_col_sum :
    ∀ k : Fin (n - 1),
      (∑ i : Fin n, S i k) =
        if k.val < r then (-2 : Int) else (-1 : Int)

/--
Auxiliary `±1` matrix in the restricted `q = 1` construction, before the
special matching correction.
-/
def ordinaryQeq1AuxDegree (n r : Nat) (i : Fin n) : Nat :=
  if i.val < r - 1 then
    (r - 3) / 2
  else if i.val < r then
    (r - 1) / 2
  else
    (n + r - 3) / 2

structure UniformColumnDegreeMatrixData
    (rows cols h : Nat) (rowDegree : Fin rows → Nat) where
  G : Fin rows → Fin cols → Nat
  G_zero_one : ∀ i k, G i k = 0 ∨ G i k = 1
  G_row_sum : ∀ i : Fin rows, (∑ k : Fin cols, G i k) = rowDegree i
  G_col_sum : ∀ k : Fin cols, (∑ i : Fin rows, G i k) = h

/--
Starting offset for the cyclic-interval realization of a `0/1` matrix with
prescribed row degrees and uniform column degree.
-/
def uniformColumnDegreePrefix {rows : Nat}
    (rowDegree : Fin rows → Nat) (i : Fin rows) : Nat :=
  ∑ j : Fin rows, if j.val < i.val then rowDegree j else 0

def uniformColumnDegreeCellMap {rows cols : Nat}
    (hcols : 0 < cols) (rowDegree : Fin rows → Nat) (i : Fin rows)
    (t : Fin (rowDegree i)) : Fin cols :=
  ⟨(uniformColumnDegreePrefix rowDegree i + t.val) % cols,
    Nat.mod_lt _ hcols⟩

def uniformColumnDegreeCellSet {rows cols : Nat}
    (hcols : 0 < cols) (rowDegree : Fin rows → Nat) (i : Fin rows) :
    Finset (Fin cols) :=
  (Finset.univ : Finset (Fin (rowDegree i))).image
    (uniformColumnDegreeCellMap hcols rowDegree i)

def uniformColumnDegreeMatrix {rows cols : Nat}
    (hcols : 0 < cols) (rowDegree : Fin rows → Nat) :
    Fin rows → Fin cols → Nat :=
  fun i k =>
    if k ∈ uniformColumnDegreeCellSet hcols rowDegree i then 1 else 0

structure OrdinaryQeq1AuxDegreeMatrixData (n r : Nat) where
  G : Fin n → Fin (n - 1) → Nat
  G_zero_one : ∀ i k, G i k = 0 ∨ G i k = 1
  G_row_sum :
    ∀ i : Fin n,
      (∑ k : Fin (n - 1), G i k) =
        if i.val < r - 1 then
          (r - 3) / 2
        else if i.val < r then
          (r - 1) / 2
        else
          (n + r - 3) / 2
  G_col_sum :
    ∀ k : Fin (n - 1), (∑ i : Fin n, G i k) = (n - 2) / 2

namespace UniformColumnDegreeMatrixData

def toOrdinaryQeq1AuxDegreeMatrixData {n r : Nat}
    (M : UniformColumnDegreeMatrixData
      n (n - 1) ((n - 2) / 2) (ordinaryQeq1AuxDegree n r)) :
    OrdinaryQeq1AuxDegreeMatrixData n r where
  G := M.G
  G_zero_one := M.G_zero_one
  G_row_sum := by
    intro i
    simpa [ordinaryQeq1AuxDegree] using M.G_row_sum i
  G_col_sum := M.G_col_sum

end UniformColumnDegreeMatrixData

structure OrdinaryQeq1AuxMatrixData (n r : Nat) where
  B : Fin n → Fin (n - 1) → Int
  B_pm_one : ∀ i k, B i k = (-1 : Int) ∨ B i k = 1
  B_row_sum :
    ∀ i : Fin n,
      (∑ k : Fin (n - 1), B i k) =
        if i.val < r - 1 then
          (r : Int) - 2 - (n : Int)
        else if i.val < r then
          (r : Int) - (n : Int)
        else
          (r : Int) - 2
  B_col_sum :
    ∀ k : Fin (n - 1), (∑ i : Fin n, B i k) = (-2 : Int)

namespace OrdinaryQeq1AuxDegreeMatrixData

theorem odd_r_of_odd_n_add_one_and_odd_n_add_r
    {n r : Nat} (hdodd : Odd (n + 1)) (hmodd : Odd (n + r)) :
    Odd r := by
  rcases hdodd with ⟨a, ha⟩
  rcases hmodd with ⟨b, hb⟩
  refine ⟨b - a, ?_⟩
  omega

theorem sum_signed_zero_one {ι : Type*} [Fintype ι]
    (g : ι → Nat) (h01 : ∀ x, g x = 0 ∨ g x = 1) :
    (∑ x : ι, if g x = 1 then (1 : Int) else (-1 : Int))
      = 2 * (∑ x : ι, (g x : Int)) - (Fintype.card ι : Int) := by
  calc
    (∑ x : ι, if g x = 1 then (1 : Int) else (-1 : Int))
        = ∑ x : ι, (2 * (g x : Int) - 1) := by
            apply Finset.sum_congr rfl
            intro x _hx
            rcases h01 x with h | h <;> simp [h]
    _ = 2 * (∑ x : ι, (g x : Int)) - (Fintype.card ι : Int) := by
            rw [Finset.sum_sub_distrib]
            simp [Finset.mul_sum]

def toAuxMatrixData {n r : Nat}
    (G : OrdinaryQeq1AuxDegreeMatrixData n r)
    (hdodd : Odd (n + 1)) (hmodd : Odd (n + r)) :
    OrdinaryQeq1AuxMatrixData n r where
  B := fun i k => if G.G i k = 1 then (1 : Int) else (-1 : Int)
  B_pm_one := by
    intro i k
    by_cases h : G.G i k = 1 <;> simp [h]
  B_row_sum := by
    intro i
    have hsum :=
      sum_signed_zero_one (fun k : Fin (n - 1) => G.G i k)
        (fun k => G.G_zero_one i k)
    change
      (∑ k : Fin (n - 1),
        if G.G i k = 1 then (1 : Int) else (-1 : Int)) =
        if i.val < r - 1 then
          (r : Int) - 2 - (n : Int)
        else if i.val < r then
          (r : Int) - (n : Int)
        else
          (r : Int) - 2
    rw [hsum]
    have hrowEq :
        (∑ x : Fin (n - 1),
          ((fun k : Fin (n - 1) => G.G i k) x : Int))
          =
          ((if i.val < r - 1 then
              (r - 3) / 2
            else if i.val < r then
              (r - 1) / 2
            else
              (n + r - 3) / 2 : Nat) : Int) := by
      simpa using congrArg (fun z : Nat => (z : Int)) (G.G_row_sum i)
    have hrodd : Odd r :=
      odd_r_of_odd_n_add_one_and_odd_n_add_r hdodd hmodd
    rcases hdodd with ⟨a, ha⟩
    rcases hrodd with ⟨s, hs⟩
    rw [hrowEq]
    by_cases hlow : i.val < r - 1
    · simp [hlow]
      omega
    · by_cases hmid : i.val < r
      · simp [hlow, hmid]
        omega
      · simp [hlow, hmid]
        omega
  B_col_sum := by
    intro k
    have hsum :=
      sum_signed_zero_one (fun i : Fin n => G.G i k)
        (fun i => G.G_zero_one i k)
    change
      (∑ i : Fin n,
        if G.G i k = 1 then (1 : Int) else (-1 : Int)) =
        (-2 : Int)
    rw [hsum]
    have hcolEq :
        (∑ x : Fin n, ((fun i : Fin n => G.G i k) x : Int))
          = (((n - 2) / 2 : Nat) : Int) := by
      simpa using congrArg (fun z : Nat => (z : Int)) (G.G_col_sum k)
    rw [hcolEq]
    rcases hdodd with ⟨a, ha⟩
    have hkpos : 0 < n - 1 := Nat.lt_of_le_of_lt (Nat.zero_le k.val) k.isLt
    simp [Fintype.card_fin]
    omega

end OrdinaryQeq1AuxDegreeMatrixData

namespace OrdinaryQeq1AuxMatrixData

def posCols {n r : Nat} (A : OrdinaryQeq1AuxMatrixData n r)
    (i : Fin n) : Finset (Fin (n - 1)) :=
  Finset.univ.filter fun k => A.B i k = 1

def posRows {n r : Nat} (A : OrdinaryQeq1AuxMatrixData n r)
    (k : Fin (n - 1)) : Finset (Fin n) :=
  Finset.univ.filter fun i => A.B i k = 1

theorem sum_row_eq_two_posCols_card_sub {n r : Nat}
    (A : OrdinaryQeq1AuxMatrixData n r) (i : Fin n) :
    (∑ k : Fin (n - 1), A.B i k) =
      2 * ((A.posCols i).card : Int) - (n - 1 : Nat) := by
  have hpoint : ∀ k : Fin (n - 1),
      A.B i k = 2 * (if A.B i k = 1 then (1 : Int) else 0) - 1 := by
    intro k
    rcases A.B_pm_one i k with h | h <;> simp [h]
  have hcountNat :
      (∑ k : Fin (n - 1), if A.B i k = 1 then (1 : Nat) else 0) =
        (A.posCols i).card := by
    rw [← Finset.card_filter]
    rfl
  have hcountInt :
      (∑ k : Fin (n - 1), if A.B i k = 1 then (1 : Int) else 0) =
        ((A.posCols i).card : Int) := by
    exact_mod_cast hcountNat
  calc
    (∑ k : Fin (n - 1), A.B i k)
        = ∑ k : Fin (n - 1),
            (2 * (if A.B i k = 1 then (1 : Int) else 0) - 1) := by
            apply Finset.sum_congr rfl
            intro k _hk
            exact hpoint k
    _ = 2 * (∑ k : Fin (n - 1),
            if A.B i k = 1 then (1 : Int) else 0) -
          (Fintype.card (Fin (n - 1)) : Int) := by
            rw [Finset.sum_sub_distrib]
            congr 1
            · rw [← Finset.mul_sum]
            · simp [Finset.sum_const]
    _ = 2 * ((A.posCols i).card : Int) - (n - 1 : Nat) := by
            rw [hcountInt]
            simp [Fintype.card_fin]

theorem sum_col_eq_two_posRows_card_sub {n r : Nat}
    (A : OrdinaryQeq1AuxMatrixData n r) (k : Fin (n - 1)) :
    (∑ i : Fin n, A.B i k) =
      2 * ((A.posRows k).card : Int) - (n : Int) := by
  have hpoint : ∀ i : Fin n,
      A.B i k = 2 * (if A.B i k = 1 then (1 : Int) else 0) - 1 := by
    intro i
    rcases A.B_pm_one i k with h | h <;> simp [h]
  have hcountNat :
      (∑ i : Fin n, if A.B i k = 1 then (1 : Nat) else 0) =
        (A.posRows k).card := by
    rw [← Finset.card_filter]
    rfl
  have hcountInt :
      (∑ i : Fin n, if A.B i k = 1 then (1 : Int) else 0) =
        ((A.posRows k).card : Int) := by
    exact_mod_cast hcountNat
  calc
    (∑ i : Fin n, A.B i k)
        = ∑ i : Fin n,
            (2 * (if A.B i k = 1 then (1 : Int) else 0) - 1) := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact hpoint i
    _ = 2 * (∑ i : Fin n,
            if A.B i k = 1 then (1 : Int) else 0) -
          (Fintype.card (Fin n) : Int) := by
            rw [Finset.sum_sub_distrib]
            congr 1
            · rw [← Finset.mul_sum]
            · simp [Finset.sum_const]
    _ = 2 * ((A.posRows k).card : Int) - (n : Int) := by
            rw [hcountInt]
            simp [Fintype.card_fin]

theorem posRows_card {n r : Nat}
    (A : OrdinaryQeq1AuxMatrixData n r) (k : Fin (n - 1)) :
    (A.posRows k).card = (n - 2) / 2 := by
  have hsum := A.sum_col_eq_two_posRows_card_sub k
  rw [A.B_col_sum k] at hsum
  have htwo : 2 * ((A.posRows k).card : Int) = (n : Int) - 2 := by
    omega
  by_cases hn : n = 0
  · subst n
    exact Fin.elim0 k
  · by_cases hn1 : n = 1
    · subst n
      exact Fin.elim0 k
    · rcases Nat.even_or_odd n with hnEven | hnOdd
      · rcases hnEven with ⟨a, ha⟩
        subst n
        have hcard : (A.posRows k).card = a - 1 := by omega
        have hdiv : (2 * a - 2) / 2 = a - 1 := by omega
        omega
      · rcases hnOdd with ⟨a, ha⟩
        subst n
        omega

theorem posCols_card {n r : Nat}
    (A : OrdinaryQeq1AuxMatrixData n r)
    (hdodd : Odd (n + 1)) (hmodd : Odd (n + r)) (i : Fin n) :
    (A.posCols i).card = ordinaryQeq1AuxDegree n r i := by
  have hsum := A.sum_row_eq_two_posCols_card_sub i
  rw [A.B_row_sum i] at hsum
  have htwo :
      2 * ((A.posCols i).card : Int) =
        (if i.val < r - 1 then
          (r : Int) - 2 - (n : Int)
        else if i.val < r then
          (r : Int) - (n : Int)
        else
          (r : Int) - 2) + (n - 1 : Nat) := by
    omega
  have hrodd : Odd r :=
    OrdinaryQeq1AuxDegreeMatrixData.odd_r_of_odd_n_add_one_and_odd_n_add_r
      hdodd hmodd
  unfold ordinaryQeq1AuxDegree
  by_cases hlow : i.val < r - 1
  · simp only [hlow, ↓reduceIte]
    rcases hrodd with ⟨s, hs⟩
    subst r
    have hcard : (A.posCols i).card = s - 1 := by omega
    have hdiv : (2 * s + 1 - 3) / 2 = s - 1 := by omega
    omega
  · by_cases hmid : i.val < r
    · simp only [hlow, hmid, ↓reduceIte]
      rcases hrodd with ⟨s, hs⟩
      subst r
      have hcard : (A.posCols i).card = s := by omega
      have hdiv : (2 * s + 1 - 1) / 2 = s := by omega
      omega
    · simp only [hlow, hmid, ↓reduceIte]
      rcases hdodd with ⟨a, ha⟩
      rcases hrodd with ⟨s, hs⟩
      have hn : n = 2 * a := by omega
      have hr : r = 2 * s + 1 := by omega
      subst n
      subst r
      have hcard : (A.posCols i).card = a + s - 1 := by omega
      have hdiv :
          (2 * a + (2 * s + 1) - 3) / 2 = a + s - 1 := by
        omega
      omega

def lowCols (n r : Nat) : Finset (Fin (n - 1)) :=
  Finset.univ.filter fun k => k.val < r

def highCols (n r : Nat) : Finset (Fin (n - 1)) :=
  Finset.univ.filter fun k => r ≤ k.val

theorem lowCols_card {n r : Nat} (hrlt : r < n) :
    (lowCols n r).card = r := by
  dsimp [lowCols]
  rw [Finset.card_filter]
  rw [sum_fin_indicator_val_lt]
  omega

theorem highCols_eq_lowCols_compl {n r : Nat} :
    highCols n r = (lowCols n r)ᶜ := by
  ext k
  by_cases h : k.val < r
  · have hn : ¬ r ≤ k.val := by omega
    simp [highCols, lowCols, hn]
  · have hp : r ≤ k.val := by omega
    simp [highCols, lowCols, hp]

theorem highCols_card {n r : Nat} (hrlt : r < n) :
    (highCols n r).card = n - 1 - r := by
  rw [highCols_eq_lowCols_compl, Finset.card_compl, lowCols_card hrlt]
  simp [Fintype.card_fin]

def pRows (n r : Nat) : Finset (Fin n) :=
  Finset.univ.filter fun i => r ≤ i.val

theorem pRows_card {n r : Nat} (hrlt : r < n) :
    (pRows n r).card = n - r := by
  dsimp [pRows]
  rw [Finset.card_filter]
  have hlt :
      (∑ i : Fin n, if i.val < r then (1 : Nat) else 0) = r := by
    rw [sum_fin_indicator_val_lt]
    omega
  have hpartition :
      (∑ i : Fin n, if r ≤ i.val then (1 : Nat) else 0) +
        (∑ i : Fin n, if i.val < r then (1 : Nat) else 0) = n := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ x : Fin n,
          ((if r ≤ x.val then (1 : Nat) else 0) +
            if x.val < r then 1 else 0))
          = ∑ _x : Fin n, (1 : Nat) := by
            apply Finset.sum_congr rfl
            intro x _hx
            by_cases hxlt : x.val < r
            · have hxge : ¬ r ≤ x.val := by omega
              simp [hxlt, hxge]
            · have hxge : r ≤ x.val := by omega
              simp [hxlt, hxge]
      _ = n := by simp
  omega

theorem pRows_card_eq_highCols_card_succ {n r : Nat} (hrlt : r < n) :
    (pRows n r).card = (highCols n r).card + 1 := by
  rw [pRows_card hrlt, highCols_card hrlt]
  omega

def pRowNeighbors {n r : Nat} (A : OrdinaryQeq1AuxMatrixData n r)
    (X : Finset (Fin n)) : Finset (Fin (n - 1)) :=
  X.biUnion fun i => A.posCols i

theorem exists_distinguished_low_neg {n r : Nat}
    (A : OrdinaryQeq1AuxMatrixData n r)
    (hdodd : Odd (n + 1)) (hmodd : Odd (n + r))
    (hrlt : r < n) (hrpos : 0 < r) :
    ∃ k : Fin (n - 1), k.val < r ∧
      A.B ⟨r - 1, by omega⟩ k = (-1 : Int) := by
  let row : Fin n := ⟨r - 1, by omega⟩
  by_contra hnone
  have hsubset : lowCols n r ⊆ A.posCols row := by
    intro k hk
    have hklt : k.val < r := by simpa [lowCols] using hk
    rcases A.B_pm_one row k with hB | hB
    · exfalso
      apply hnone
      exact ⟨k, hklt, hB⟩
    · simp [posCols, hB]
  have hcardle := Finset.card_le_card hsubset
  have hposCard := A.posCols_card hdodd hmodd row
  have hlowCard := lowCols_card (n := n) (r := r) hrlt
  rw [hlowCard, hposCard] at hcardle
  unfold ordinaryQeq1AuxDegree at hcardle
  have hnotLow : ¬ row.val < r - 1 := by
    simp [row]
  have hmid : row.val < r := by
    simp [row]
    omega
  simp [hnotLow, hmid] at hcardle
  omega

theorem pRow_posCols_card {n r : Nat}
    (A : OrdinaryQeq1AuxMatrixData n r)
    (hdodd : Odd (n + 1)) (hmodd : Odd (n + r))
    {i : Fin n} (hi : r ≤ i.val) :
    (A.posCols i).card = (n + r - 3) / 2 := by
  have h := A.posCols_card hdodd hmodd i
  unfold ordinaryQeq1AuxDegree at h
  have hlow : ¬ i.val < r - 1 := by omega
  have hmid : ¬ i.val < r := by omega
  simpa [hlow, hmid] using h

theorem pRow_posCols_card_pos {n r : Nat}
    (A : OrdinaryQeq1AuxMatrixData n r)
    (hdodd : Odd (n + 1)) (hd5 : 5 ≤ n + 1) (hmodd : Odd (n + r))
    (hrpos : 0 < r) {i : Fin n} (hi : r ≤ i.val) :
    0 < (A.posCols i).card := by
  rw [A.pRow_posCols_card hdodd hmodd hi]
  have hrodd : Odd r :=
    OrdinaryQeq1AuxDegreeMatrixData.odd_r_of_odd_n_add_one_and_odd_n_add_r
      hdodd hmodd
  rcases hdodd with ⟨a, ha⟩
  rcases hrodd with ⟨s, hs⟩
  have hn : n = 2 * a := by omega
  have hr : r = 2 * s + 1 := by omega
  subst n
  subst r
  omega

theorem posRows_card_le_pRow_posCols_card {n r : Nat}
    (A : OrdinaryQeq1AuxMatrixData n r)
    (hdodd : Odd (n + 1)) (hmodd : Odd (n + r))
    (hrpos : 0 < r) {i : Fin n} (hi : r ≤ i.val) (k : Fin (n - 1)) :
    (A.posRows k).card ≤ (A.posCols i).card := by
  rw [A.posRows_card k, A.pRow_posCols_card hdodd hmodd hi]
  have hrodd : Odd r :=
    OrdinaryQeq1AuxDegreeMatrixData.odd_r_of_odd_n_add_one_and_odd_n_add_r
      hdodd hmodd
  rcases hdodd with ⟨a, ha⟩
  rcases hrodd with ⟨s, hs⟩
  have hn : n = 2 * a := by omega
  have hr : r = 2 * s + 1 := by omega
  subst n
  subst r
  omega

theorem posRows_card_lt_pRow_posCols_card_of_one_lt_r {n r : Nat}
    (A : OrdinaryQeq1AuxMatrixData n r)
    (hdodd : Odd (n + 1)) (hmodd : Odd (n + r))
    (hr1 : 1 < r) {i : Fin n} (hi : r ≤ i.val) (k : Fin (n - 1)) :
    (A.posRows k).card < (A.posCols i).card := by
  rw [A.posRows_card k, A.pRow_posCols_card hdodd hmodd hi]
  have hrodd : Odd r :=
    OrdinaryQeq1AuxDegreeMatrixData.odd_r_of_odd_n_add_one_and_odd_n_add_r
      hdodd hmodd
  rcases hdodd with ⟨a, ha⟩
  rcases hrodd with ⟨s, hs⟩
  have hn : n = 2 * a := by omega
  have hr : r = 2 * s + 1 := by omega
  subst n
  subst r
  omega

theorem pRows_hall {n r : Nat}
    (A : OrdinaryQeq1AuxMatrixData n r)
    (hdodd : Odd (n + 1)) (hd5 : 5 ≤ n + 1) (hmodd : Odd (n + r))
    (hrpos : 0 < r) (X : Finset (Fin n)) (hX : X ⊆ pRows n r) :
    X.card ≤ (A.pRowNeighbors X).card := by
  classical
  let N := A.pRowNeighbors X
  let degP : Nat := (n + r - 3) / 2
  let degC : Nat := (n - 2) / 2
  have hrodd : Odd r :=
    OrdinaryQeq1AuxDegreeMatrixData.odd_r_of_odd_n_add_one_and_odd_n_add_r
      hdodd hmodd
  have hdegP_pos : 0 < degP := by
    rcases hdodd with ⟨a, ha⟩
    rcases hrodd with ⟨s, hs⟩
    have hn : n = 2 * a := by omega
    have hr : r = 2 * s + 1 := by omega
    subst n
    subst r
    omega
  have hdegC_le : degC ≤ degP := by
    rcases hdodd with ⟨a, ha⟩
    rcases hrodd with ⟨s, hs⟩
    have hn : n = 2 * a := by omega
    have hr : r = 2 * s + 1 := by omega
    subst n
    subst r
    omega
  have hrow :
      ∀ i ∈ X, (A.posCols i).card = degP := by
    intro i hi
    have hip : r ≤ i.val := by
      have hmem := hX hi
      simpa [pRows] using hmem
    exact A.pRow_posCols_card hdodd hmodd hip
  have hrowSum :
      (∑ i ∈ X, (A.posCols i).card) = X.card * degP := by
    calc
      (∑ i ∈ X, (A.posCols i).card)
          = ∑ _i ∈ X, degP := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hrow i hi
      _ = X.card * degP := by simp
  have hrowRestrict :
      ∀ i ∈ X,
        (∑ k ∈ N, if A.B i k = 1 then (1 : Nat) else 0) =
          (A.posCols i).card := by
    intro i hi
    rw [← Finset.card_filter]
    have hfilter :
        N.filter (fun k : Fin (n - 1) => A.B i k = 1) = A.posCols i := by
      ext k
      constructor
      · intro hk
        have hkB : A.B i k = 1 := by
          exact (Finset.mem_filter.mp hk).2
        simp [posCols, hkB]
      · intro hk
        have hkB : A.B i k = 1 := by simpa [posCols] using hk
        have hkN : k ∈ N := by
          exact Finset.mem_biUnion.mpr ⟨i, hi, hk⟩
        simp [hkN, hkB]
    rw [hfilter]
  have hcolBound :
      ∀ k ∈ N, (∑ i ∈ X, if A.B i k = 1 then (1 : Nat) else 0) ≤ degC := by
    intro k _hk
    rw [← Finset.card_filter]
    have hsubset :
        X.filter (fun i : Fin n => A.B i k = 1) ⊆ A.posRows k := by
      intro i hi
      have hB : A.B i k = 1 := by
        exact (Finset.mem_filter.mp hi).2
      simp [posRows, hB]
    have hcardle := Finset.card_le_card hsubset
    rw [A.posRows_card k] at hcardle
    exact hcardle
  have hedge_eq :
      (∑ i ∈ X, (A.posCols i).card) =
        ∑ k ∈ N, ∑ i ∈ X, if A.B i k = 1 then (1 : Nat) else 0 := by
    calc
      (∑ i ∈ X, (A.posCols i).card)
          = ∑ i ∈ X, ∑ k ∈ N,
              if A.B i k = 1 then (1 : Nat) else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              exact (hrowRestrict i hi).symm
      _ = ∑ k ∈ N, ∑ i ∈ X,
              if A.B i k = 1 then (1 : Nat) else 0 := by
              rw [Finset.sum_comm]
  have hedge_le : X.card * degP ≤ N.card * degC := by
    rw [← hrowSum, hedge_eq]
    calc
      (∑ k ∈ N, ∑ i ∈ X, if A.B i k = 1 then (1 : Nat) else 0)
          ≤ ∑ _k ∈ N, degC := by
              apply Finset.sum_le_sum
              intro k hk
              exact hcolBound k hk
      _ = N.card * degC := by simp [Nat.mul_comm]
  have hmul : X.card * degP ≤ N.card * degP :=
    le_trans hedge_le (Nat.mul_le_mul_left N.card hdegC_le)
  exact Nat.le_of_mul_le_mul_right hmul hdegP_pos

theorem exists_pRows_matching {n r : Nat}
    (A : OrdinaryQeq1AuxMatrixData n r)
    (hdodd : Odd (n + 1)) (hd5 : 5 ≤ n + 1) (hmodd : Odd (n + r))
    (hrpos : 0 < r) :
    ∃ f : {i : Fin n // i ∈ pRows n r} → Fin (n - 1),
      Function.Injective f ∧ ∀ i, A.B i.1 (f i) = 1 := by
  classical
  let P := {i : Fin n // i ∈ pRows n r}
  let neigh : P → Finset (Fin (n - 1)) := fun i => A.posCols i.1
  have hHall :
      ∀ S : Finset P, S.card ≤ (S.biUnion neigh).card := by
    intro S
    let X : Finset (Fin n) := S.image fun i : P => i.1
    have hcardX : X.card = S.card := by
      dsimp [X]
      exact Finset.card_image_of_injective
        S (fun a b h => Subtype.ext h)
    have hX : X ⊆ pRows n r := by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨x, hx, rfl⟩
      exact x.2
    have hneigh :
        (S.biUnion neigh).card = (A.pRowNeighbors X).card := by
      congr 1
      ext k
      constructor
      · intro hk
        rcases Finset.mem_biUnion.mp hk with ⟨i, hiS, hik⟩
        exact Finset.mem_biUnion.mpr
          ⟨i.1, Finset.mem_image.mpr ⟨i, hiS, rfl⟩, hik⟩
      · intro hk
        rcases Finset.mem_biUnion.mp hk with ⟨i, hiX, hik⟩
        rcases Finset.mem_image.mp hiX with ⟨j, hjS, hji⟩
        subst i
        exact Finset.mem_biUnion.mpr ⟨j, hjS, hik⟩
    rw [← hcardX, hneigh]
    exact A.pRows_hall hdodd hd5 hmodd hrpos X hX
  rcases (Finset.all_card_le_biUnion_card_iff_existsInjective' neigh).mp
      hHall with ⟨f, hfInj, hfMem⟩
  refine ⟨f, hfInj, ?_⟩
  intro i
  simpa [neigh, posCols] using hfMem i

theorem pRow_exists_distinguished_neg_pos {n r : Nat}
    (A : OrdinaryQeq1AuxMatrixData n r)
    (hdodd : Odd (n + 1)) (hd5 : 5 ≤ n + 1) (hmodd : Odd (n + r))
    (hrlt : r < n) (hrpos : 0 < r) {i : Fin n} (hi : r ≤ i.val) :
    ∃ k : Fin (n - 1),
      A.B i k = 1 ∧ A.B ⟨r - 1, by omega⟩ k = (-1 : Int) := by
  let nu : Fin n := ⟨r - 1, by omega⟩
  by_contra hnone
  have hsubset : A.posCols i ⊆ A.posCols nu := by
    intro k hk
    have hBi : A.B i k = 1 := by
      simpa [posCols] using hk
    rcases A.B_pm_one nu k with hnu | hnu
    · exfalso
      exact hnone ⟨k, hBi, hnu⟩
    · simp [posCols, hnu]
  have hcardle := Finset.card_le_card hsubset
  have hp := A.pRow_posCols_card hdodd hmodd hi
  have hnu := A.posCols_card hdodd hmodd nu
  have hnu_low : ¬ nu.val < r - 1 := by
    simp [nu]
  have hnu_mid : nu.val < r := by
    simp [nu]
    omega
  have hnuCard : (A.posCols nu).card = (r - 1) / 2 := by
    simpa [ordinaryQeq1AuxDegree, hnu_low, hnu_mid] using hnu
  rw [hp, hnuCard] at hcardle
  have hgt : (r - 1) / 2 < (n + r - 3) / 2 := by
    have hrodd : Odd r :=
      OrdinaryQeq1AuxDegreeMatrixData.odd_r_of_odd_n_add_one_and_odd_n_add_r
        hdodd hmodd
    rcases hdodd with ⟨a, ha⟩
    rcases hrodd with ⟨s, hs⟩
    have hn : n = 2 * a := by omega
    have hr : r = 2 * s + 1 := by omega
    subst n
    subst r
    omega
  omega

end OrdinaryQeq1AuxMatrixData

/--
Paper-facing output for the restricted `q = 1` matching correction before the
final `+1` and `-1` edits are applied.  Rows with `r <= i.val` are the `P` rows, the
row with `i.val = r - 1` is the distinguished row, and columns with
`r <= k.val` are the non-special matched columns after relabelling.
-/
structure OrdinaryQeq1CanonicalCorrectionData (n r : Nat) where
  B : Fin n → Fin (n - 1) → Int
  mate : Fin n → Fin (n - 1)
  special : Fin n
  B_pm_one : ∀ i k, B i k = (-1 : Int) ∨ B i k = 1
  B_row_sum :
    ∀ i : Fin n,
      (∑ k : Fin (n - 1), B i k) =
        if i.val < r - 1 then
          (r : Int) - 2 - (n : Int)
        else if i.val < r then
          (r : Int) - (n : Int)
        else
          (r : Int) - 2
  B_col_sum :
    ∀ k : Fin (n - 1), (∑ i : Fin n, B i k) = (-2 : Int)
  mate_pos : ∀ i : Fin n, r ≤ i.val → B i (mate i) = 1
  mate_col_sum :
    ∀ k : Fin (n - 1),
      (∑ i : Fin n,
        if r ≤ i.val ∧ mate i = k then (1 : Int) else 0)
        = if k.val < r then
            if k = mate special then (1 : Int) else 0
          else
            1
  special_mem : r ≤ special.val
  special_low : (mate special).val < r
  special_neg :
    ∀ i : Fin n, i.val = r - 1 → B i (mate special) = (-1 : Int)

structure OrdinaryQeq1SpecialMatchingData {n r : Nat}
    (A : OrdinaryQeq1AuxMatrixData n r) where
  mate : Fin n → Fin (n - 1)
  special : Fin n
  mate_pos : ∀ i : Fin n, r ≤ i.val → A.B i (mate i) = 1
  mate_col_sum :
    ∀ k : Fin (n - 1),
      (∑ i : Fin n,
        if r ≤ i.val ∧ mate i = k then (1 : Int) else 0)
        = if k.val < r then
            if k = mate special then (1 : Int) else 0
          else
            1
  special_mem : r ≤ special.val
  special_low : (mate special).val < r
  special_neg :
    ∀ i : Fin n, i.val = r - 1 → A.B i (mate special) = (-1 : Int)

structure OrdinaryQeq1PRowSpecialMatchingData {n r : Nat}
    (A : OrdinaryQeq1AuxMatrixData n r) where
  mate : Fin n → Fin (n - 1)
  special : Fin n
  mate_pos : ∀ i : Fin n, r ≤ i.val → A.B i (mate i) = 1
  mate_col_sum_pRows :
    ∀ k : Fin (n - 1),
      (∑ i ∈ OrdinaryQeq1AuxMatrixData.pRows n r,
        if mate i = k then (1 : Int) else 0)
        = if k.val < r then
            if k = mate special then (1 : Int) else 0
          else
            1
  special_mem : r ≤ special.val
  special_low : (mate special).val < r
  special_neg :
    ∀ i : Fin n, i.val = r - 1 → A.B i (mate special) = (-1 : Int)

structure OrdinaryQeq1AuxSpecialMatchingData (n r : Nat) where
  aux : OrdinaryQeq1AuxMatrixData n r
  matching : OrdinaryQeq1SpecialMatchingData aux

structure OrdinaryQeq1AuxPRowSpecialMatchingData (n r : Nat) where
  aux : OrdinaryQeq1AuxMatrixData n r
  matching : OrdinaryQeq1PRowSpecialMatchingData aux

namespace OrdinaryQeq1SpecialMatchingData

def toCorrectionData {n r : Nat} {A : OrdinaryQeq1AuxMatrixData n r}
    (M : OrdinaryQeq1SpecialMatchingData A) :
    OrdinaryQeq1CanonicalCorrectionData n r where
  B := A.B
  mate := M.mate
  special := M.special
  B_pm_one := A.B_pm_one
  B_row_sum := A.B_row_sum
  B_col_sum := A.B_col_sum
  mate_pos := M.mate_pos
  mate_col_sum := M.mate_col_sum
  special_mem := M.special_mem
  special_low := M.special_low
  special_neg := M.special_neg

end OrdinaryQeq1SpecialMatchingData

namespace OrdinaryQeq1PRowSpecialMatchingData

theorem mate_col_sum_high {n r : Nat} {A : OrdinaryQeq1AuxMatrixData n r}
    (M : OrdinaryQeq1PRowSpecialMatchingData A)
    {k : Fin (n - 1)} (hk : r ≤ k.val) :
    (∑ i ∈ OrdinaryQeq1AuxMatrixData.pRows n r,
      if M.mate i = k then (1 : Int) else 0) = 1 := by
  have hnot : ¬ k.val < r := by omega
  simpa [hnot] using M.mate_col_sum_pRows k

theorem mate_col_sum_special {n r : Nat} {A : OrdinaryQeq1AuxMatrixData n r}
    (M : OrdinaryQeq1PRowSpecialMatchingData A) :
    (∑ i ∈ OrdinaryQeq1AuxMatrixData.pRows n r,
      if M.mate i = M.mate M.special then (1 : Int) else 0) = 1 := by
  simpa [M.special_low] using M.mate_col_sum_pRows (M.mate M.special)

theorem mate_col_sum_low_ne_special {n r : Nat}
    {A : OrdinaryQeq1AuxMatrixData n r}
    (M : OrdinaryQeq1PRowSpecialMatchingData A)
    {k : Fin (n - 1)} (hk : k.val < r) (hne : k ≠ M.mate M.special) :
    (∑ i ∈ OrdinaryQeq1AuxMatrixData.pRows n r,
      if M.mate i = k then (1 : Int) else 0) = 0 := by
  simpa [hk, hne] using M.mate_col_sum_pRows k

def toSpecialMatchingData {n r : Nat} {A : OrdinaryQeq1AuxMatrixData n r}
    (M : OrdinaryQeq1PRowSpecialMatchingData A) :
    OrdinaryQeq1SpecialMatchingData A where
  mate := M.mate
  special := M.special
  mate_pos := M.mate_pos
  mate_col_sum := by
    intro k
    calc
      (∑ i : Fin n,
        if r ≤ i.val ∧ M.mate i = k then (1 : Int) else 0)
          = ∑ i : Fin n,
              if r ≤ i.val then
                if M.mate i = k then (1 : Int) else 0
              else
                0 := by
              apply Finset.sum_congr rfl
              intro i _hi
              by_cases hr : r ≤ i.val
              · by_cases hm : M.mate i = k <;> simp [hr, hm]
              · simp [hr]
      _ = ∑ i ∈ OrdinaryQeq1AuxMatrixData.pRows n r,
              if M.mate i = k then (1 : Int) else 0 := by
              rw [OrdinaryQeq1AuxMatrixData.pRows, Finset.sum_filter]
      _ = if k.val < r then
            if k = M.mate M.special then (1 : Int) else 0
          else
            1 := M.mate_col_sum_pRows k
  special_mem := M.special_mem
  special_low := M.special_low
  special_neg := M.special_neg

end OrdinaryQeq1PRowSpecialMatchingData

namespace OrdinaryQeq1AuxSpecialMatchingData

def toCorrectionData {n r : Nat}
    (D : OrdinaryQeq1AuxSpecialMatchingData n r) :
    OrdinaryQeq1CanonicalCorrectionData n r :=
  D.matching.toCorrectionData

end OrdinaryQeq1AuxSpecialMatchingData

namespace OrdinaryQeq1AuxPRowSpecialMatchingData

def toAuxSpecialMatchingData {n r : Nat}
    (D : OrdinaryQeq1AuxPRowSpecialMatchingData n r) :
    OrdinaryQeq1AuxSpecialMatchingData n r where
  aux := D.aux
  matching := D.matching.toSpecialMatchingData

end OrdinaryQeq1AuxPRowSpecialMatchingData

namespace OrdinaryQeq1CanonicalCorrectionData

def S {n r : Nat} (D : OrdinaryQeq1CanonicalCorrectionData n r)
    (i : Fin n) (k : Fin (n - 1)) : Int :=
  D.B i k
    + (if r ≤ i.val ∧ D.mate i = k then (1 : Int) else 0)
    - (if i.val = r - 1 ∧ k = D.mate D.special then (1 : Int) else 0)

theorem sum_fin_indicator_val_eq {n a : Nat} (ha : a < n) :
    (∑ i : Fin n, if i.val = a then (1 : Int) else 0) = 1 := by
  let x : Fin n := ⟨a, ha⟩
  trans ∑ i : Fin n, if i = x then (1 : Int) else 0
  · apply Finset.sum_congr rfl
    intro i _hi
    by_cases h : i.val = a
    · have hix : i = x := by
        ext
        simpa [x] using h
      simp [hix, x]
    · have hix : i ≠ x := by
        intro hix
        exact h (by simpa [x] using congrArg Fin.val hix)
      simp [h, hix]
  · simp

theorem inc_row_sum {n r : Nat}
    (D : OrdinaryQeq1CanonicalCorrectionData n r) (i : Fin n) :
    (∑ k : Fin (n - 1),
      if r ≤ i.val ∧ D.mate i = k then (1 : Int) else 0)
      = if r ≤ i.val then (1 : Int) else 0 := by
  by_cases hi : r ≤ i.val
  · simp [hi]
  · have hnone :
      ∀ k : Fin (n - 1), ¬ (r ≤ i.val ∧ D.mate i = k) := by
      intro k h
      exact hi h.1
    simp [hi]

theorem dec_row_sum {n r : Nat}
    (D : OrdinaryQeq1CanonicalCorrectionData n r) (i : Fin n) :
    (∑ k : Fin (n - 1),
      if i.val = r - 1 ∧ k = D.mate D.special then (1 : Int) else 0)
      = if i.val = r - 1 then (1 : Int) else 0 := by
  by_cases hi : i.val = r - 1
  · simp [hi]
  · have hnone :
      ∀ k : Fin (n - 1), ¬ (i.val = r - 1 ∧ k = D.mate D.special) := by
      intro k h
      exact hi h.1
    simp [hi]

theorem dec_col_sum {n r : Nat}
    (D : OrdinaryQeq1CanonicalCorrectionData n r)
    (hrlt : r < n) (hrpos : 0 < r) (k : Fin (n - 1)) :
    (∑ i : Fin n,
      if i.val = r - 1 ∧ k = D.mate D.special then (1 : Int) else 0)
      = if k = D.mate D.special then (1 : Int) else 0 := by
  by_cases hk : k = D.mate D.special
  · simp [hk, sum_fin_indicator_val_eq (n := n) (a := r - 1) (by omega)]
  · have hnone :
      ∀ i : Fin n, ¬ (i.val = r - 1 ∧ k = D.mate D.special) := by
      intro i h
      exact hk h.2
    simp [hk]

theorem S_signed {n r : Nat}
    (D : OrdinaryQeq1CanonicalCorrectionData n r)
    (hrpos : 0 < r) (i : Fin n) (k : Fin (n - 1)) :
    IsSignedVal (D.S i k) := by
  by_cases hinc : r ≤ i.val ∧ D.mate i = k
  · have hB : D.B i k = 1 := by
      rw [← hinc.2]
      exact D.mate_pos i hinc.1
    have hdec : ¬ (i.val = r - 1 ∧ k = D.mate D.special) := by
      intro h
      have : r ≤ r - 1 := by simpa [h.1] using hinc.1
      omega
    simp [S, hinc, hdec, hB, IsSignedVal, signedVals]
  · by_cases hdec : i.val = r - 1 ∧ k = D.mate D.special
    · have hB : D.B i k = (-1 : Int) := by
        rw [hdec.2]
        exact D.special_neg i hdec.1
      have hBspecial : D.B i (D.mate D.special) = (-1 : Int) := by
        exact D.special_neg i hdec.1
      have hnP : ¬ r ≤ i.val := by
        rw [hdec.1]
        omega
      have hrle : ¬ r ≤ r - 1 := by omega
      simp [S, hdec.1, hdec.2, hBspecial, hrle,
        IsSignedVal, signedVals]
    · rcases D.B_pm_one i k with hB | hB
      · simp [S, hinc, hdec, hB, IsSignedVal, signedVals]
      · simp [S, hinc, hdec, hB, IsSignedVal, signedVals]

theorem S_ge_neg_one_of_P {n r : Nat}
    (D : OrdinaryQeq1CanonicalCorrectionData n r)
    (hrpos : 0 < r) (i : Fin n) (k : Fin (n - 1))
    (hi : r ≤ i.val) :
    (-1 : Int) ≤ D.S i k := by
  have hdec : ¬ (i.val = r - 1 ∧ k = D.mate D.special) := by
    intro h
    have : r ≤ r - 1 := by simpa [h.1] using hi
    omega
  by_cases hinc : r ≤ i.val ∧ D.mate i = k
  · have hB : D.B i k = 1 := by
      rw [← hinc.2]
      exact D.mate_pos i hinc.1
    simp [S, hinc, hdec, hB]
  · rcases D.B_pm_one i k with hB | hB <;> simp [S, hinc, hdec, hB]

theorem S_row_sum {n r : Nat}
    (D : OrdinaryQeq1CanonicalCorrectionData n r)
    (hrpos : 0 < r) (i : Fin n) :
    (∑ k : Fin (n - 1), D.S i k) =
      if i.val < r - 1 then
        (r : Int) - 2 - (n : Int)
      else if i.val < r then
        (r : Int) - 1 - (n : Int)
      else
        (r : Int) - 1 := by
  have hsplit :
      (∑ k : Fin (n - 1), D.S i k)
        =
        (∑ k : Fin (n - 1), D.B i k)
          + (∑ k : Fin (n - 1),
              if r ≤ i.val ∧ D.mate i = k then (1 : Int) else 0)
          - (∑ k : Fin (n - 1),
              if i.val = r - 1 ∧ k = D.mate D.special then (1 : Int) else 0) := by
    simp [S, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hsplit, D.B_row_sum i, D.inc_row_sum i, D.dec_row_sum i]
  by_cases hlow : i.val < r - 1
  · have hnP : ¬ r ≤ i.val := by omega
    have hnu : i.val ≠ r - 1 := by omega
    simp [hlow, hnP, hnu]
  · by_cases hmid : i.val < r
    · have hnP : ¬ r ≤ i.val := by omega
      have hnu : i.val = r - 1 := by omega
      have hrle : ¬ r ≤ r - 1 := by omega
      simp [hnu, hrpos, hrle]
      ring_nf
    · have hP : r ≤ i.val := by omega
      have hnu : i.val ≠ r - 1 := by omega
      simp [hlow, hmid, hP, hnu]
      ring_nf

theorem S_col_sum {n r : Nat}
    (D : OrdinaryQeq1CanonicalCorrectionData n r)
    (hrlt : r < n) (hrpos : 0 < r) (k : Fin (n - 1)) :
    (∑ i : Fin n, D.S i k) =
      if k.val < r then (-2 : Int) else (-1 : Int) := by
  have hsplit :
      (∑ i : Fin n, D.S i k)
        =
        (∑ i : Fin n, D.B i k)
          + (∑ i : Fin n,
              if r ≤ i.val ∧ D.mate i = k then (1 : Int) else 0)
          - (∑ i : Fin n,
              if i.val = r - 1 ∧ k = D.mate D.special then (1 : Int) else 0) := by
    simp [S, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hsplit, D.B_col_sum k, D.mate_col_sum k, D.dec_col_sum hrlt hrpos k]
  by_cases hlow : k.val < r
  · by_cases hspecial : k = D.mate D.special
    · have hlow' : (D.mate D.special).val < r := D.special_low
      simp [hspecial, hlow']
    · simp [hlow, hspecial]
  · have hspecial : k ≠ D.mate D.special := by
      intro hk
      have : (D.mate D.special).val < r := D.special_low
      omega
    simp [hlow, hspecial]

def toCanonicalMatrixData {n r : Nat}
    (D : OrdinaryQeq1CanonicalCorrectionData n r)
    (hrlt : r < n) (hrpos : 0 < r) :
    OrdinaryQeq1CanonicalMatrixData n (n + r) r where
  S := D.S
  S_signed := D.S_signed hrpos
  S_ge_neg_one_of_P := D.S_ge_neg_one_of_P hrpos
  S_row_sum := D.S_row_sum hrpos
  S_col_sum := D.S_col_sum hrlt hrpos

end OrdinaryQeq1CanonicalCorrectionData

def OrdinaryQeq1AuxDegreeMatrixGoal : Prop :=
  ∀ {n r : Nat},
    Odd (n + 1) → 5 ≤ n + 1 →
    Odd (n + r) →
    r < n → 0 < r →
    Nonempty (OrdinaryQeq1AuxDegreeMatrixData n r)

def UniformColumnDegreeMatrixGoal : Prop :=
  ∀ {rows cols h : Nat} (rowDegree : Fin rows → Nat),
    0 < cols →
    (∀ i : Fin rows, rowDegree i ≤ cols) →
    (∑ i : Fin rows, rowDegree i) = h * cols →
    Nonempty (UniformColumnDegreeMatrixData rows cols h rowDegree)

def UniformColumnDegreeResidueCountGoal : Prop :=
  ∀ {rows cols h : Nat} (rowDegree : Fin rows → Nat),
    (hcols : 0 < cols) →
    (∀ i : Fin rows, rowDegree i ≤ cols) →
    (∑ i : Fin rows, rowDegree i) = h * cols →
    ∀ k : Fin cols,
      (∑ i : Fin rows,
        if k ∈ uniformColumnDegreeCellSet hcols rowDegree i then 1 else 0) = h

def UniformColumnDegreeIntervalPartitionGoal : Prop :=
  ∀ {rows cols : Nat} (rowDegree : Fin rows → Nat),
    (hcols : 0 < cols) →
    (∀ i : Fin rows, rowDegree i ≤ cols) →
    ∀ k : Fin cols,
      (∑ i : Fin rows,
        if k ∈ uniformColumnDegreeCellSet hcols rowDegree i then 1 else 0) =
      (∑ n ∈ Finset.range (∑ i : Fin rows, rowDegree i),
        if n % cols = k.val then 1 else 0)

def uniformColumnDegreeIntervalCellMap {cols : Nat}
    (hcols : 0 < cols) (start d : Nat) (t : Fin d) : Fin cols :=
  ⟨(start + t.val) % cols, Nat.mod_lt _ hcols⟩

def uniformColumnDegreeIntervalCellSet {cols : Nat}
    (hcols : 0 < cols) (start d : Nat) : Finset (Fin cols) :=
  (Finset.univ : Finset (Fin d)).image
    (uniformColumnDegreeIntervalCellMap hcols start d)

def uniformColumnDegreeShiftedCellSet {rows cols : Nat}
    (hcols : 0 < cols) (offset : Nat)
    (rowDegree : Fin rows → Nat) (i : Fin rows) : Finset (Fin cols) :=
  uniformColumnDegreeIntervalCellSet hcols
    (offset + uniformColumnDegreePrefix rowDegree i) (rowDegree i)

theorem uniformColumnDegreeIntervalCellMap_injective {cols : Nat}
    (hcols : 0 < cols) {start d : Nat} (hdle : d ≤ cols) :
    Function.Injective (uniformColumnDegreeIntervalCellMap hcols start d) := by
  intro a b hab
  apply Fin.ext
  have hval :
      (start + a.val) % cols = (start + b.val) % cols :=
    congrArg Fin.val hab
  have hmod : start + a.val ≡ start + b.val [MOD cols] := hval
  have habmod : a.val ≡ b.val [MOD cols] :=
    Nat.ModEq.add_left_cancel' start hmod
  exact Nat.ModEq.eq_of_lt_of_lt habmod
    (lt_of_lt_of_le a.is_lt hdle)
    (lt_of_lt_of_le b.is_lt hdle)

theorem uniformColumnDegreeIntervalCellResidueSum {cols : Nat}
    (hcols : 0 < cols) {start d : Nat} (hdle : d ≤ cols)
    (k : Fin cols) :
    (if k ∈ uniformColumnDegreeIntervalCellSet hcols start d then 1 else 0) =
      (∑ n ∈ Finset.Ico start (start + d),
        if n % cols = k.val then (1 : Nat) else 0) := by
  let fiber : Finset (Fin d) :=
    (Finset.univ : Finset (Fin d)).filter
      (fun t => uniformColumnDegreeIntervalCellMap hcols start d t = k)
  have hfilter :
      (Finset.Ico start (start + d)).filter (fun n => n % cols = k.val) =
        fiber.image (fun t => start + t.val) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image]
    constructor
    · intro hn
      rcases hn with ⟨⟨hlo, hhi⟩, hmod⟩
      have hnd : n - start < d := by omega
      refine ⟨⟨n - start, hnd⟩, ?_, ?_⟩
      · simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
        apply Fin.ext
        change (start + (n - start)) % cols = k.val
        have hn' : n = start + (n - start) := by omega
        calc
          (start + (n - start)) % cols = n % cols := by rw [← hn']
          _ = k.val := hmod
      · change start + (n - start) = n
        omega
    · intro hn
      rcases hn with ⟨t, ht, rfl⟩
      have htmap : uniformColumnDegreeIntervalCellMap hcols start d t = k := by
        simpa [fiber] using ht
      constructor
      · constructor <;> omega
      · simpa [uniformColumnDegreeIntervalCellMap] using congrArg Fin.val htmap
  have hsumIco :
      (∑ n ∈ Finset.Ico start (start + d),
        if n % cols = k.val then (1 : Nat) else 0) =
      ((Finset.Ico start (start + d)).filter
        (fun n => n % cols = k.val)).card := by
    rw [Finset.card_filter]
  rw [hsumIco, hfilter]
  by_cases hk : k ∈ uniformColumnDegreeIntervalCellSet hcols start d
  · rcases Finset.mem_image.mp hk with ⟨t, _htuniv, ht⟩
    have hcard : fiber.card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨t, ?_⟩
      ext u
      simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hu
        exact uniformColumnDegreeIntervalCellMap_injective hcols hdle
          (hu.trans ht.symm)
      · intro hu
        subst u
        exact ht
    rw [if_pos hk]
    rw [Finset.card_image_of_injective]
    · exact hcard.symm
    · intro a b hab
      apply Fin.ext
      exact Nat.add_left_cancel hab
  · have hempty : fiber = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro t ht
      apply hk
      exact Finset.mem_image.mpr ⟨t, by simp, by simpa [fiber] using ht⟩
    rw [if_neg hk, hempty]
    simp

theorem uniformColumnDegreePrefix_succ {n : Nat}
    (rowDegree : Fin (n + 1) → Nat) (i : Fin n) :
    uniformColumnDegreePrefix rowDegree i.succ =
      rowDegree 0 +
        uniformColumnDegreePrefix (fun j : Fin n => rowDegree j.succ) i := by
  unfold uniformColumnDegreePrefix
  rw [Fin.sum_univ_succ]
  simp [Fin.val_succ]

theorem uniformColumnDegreeShiftedIntervalPartition {rows cols : Nat}
    (rowDegree : Fin rows → Nat) (hcols : 0 < cols)
    (hrowLe : ∀ i : Fin rows, rowDegree i ≤ cols)
    (offset : Nat) (k : Fin cols) :
    (∑ i : Fin rows,
      if k ∈ uniformColumnDegreeShiftedCellSet hcols offset rowDegree i
      then 1 else 0) =
    (∑ n ∈ Finset.Ico offset
        (offset + ∑ i : Fin rows, rowDegree i),
      if n % cols = k.val then (1 : Nat) else 0) := by
  induction rows generalizing offset k with
  | zero =>
      simp
  | succ n ih =>
      let tail : Fin n → Nat := fun i => rowDegree i.succ
      let f : Nat → Nat := fun n => if n % cols = k.val then (1 : Nat) else 0
      have htailLe : ∀ i : Fin n, tail i ≤ cols := by
        intro i
        exact hrowLe i.succ
      have hfirst :=
        uniformColumnDegreeIntervalCellResidueSum
          hcols (hrowLe 0) (start := offset) (k := k)
      have htail := ih tail htailLe (offset + rowDegree 0) k
      have htailSet :
          (∑ i : Fin n,
            if k ∈ uniformColumnDegreeShiftedCellSet hcols offset
              rowDegree i.succ then 1 else 0) =
          (∑ i : Fin n,
            if k ∈ uniformColumnDegreeShiftedCellSet hcols
              (offset + rowDegree 0) tail i then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro i _hi
        have hstart :
            offset + uniformColumnDegreePrefix rowDegree i.succ =
              (offset + rowDegree 0) +
                uniformColumnDegreePrefix tail i := by
          dsimp [tail]
          rw [uniformColumnDegreePrefix_succ rowDegree i]
          omega
        simp [uniformColumnDegreeShiftedCellSet,
          uniformColumnDegreeIntervalCellSet,
          uniformColumnDegreeIntervalCellMap, tail, hstart]
      have hsumRows :
          (∑ i : Fin (n + 1), rowDegree i) =
            rowDegree 0 + ∑ i : Fin n, tail i := by
        rw [Fin.sum_univ_succ]
      have hcombine :
          (∑ n_1 ∈ Finset.Ico offset (offset + rowDegree 0), f n_1) +
            (∑ n_1 ∈ Finset.Ico (offset + rowDegree 0)
              ((offset + rowDegree 0) + ∑ i : Fin n, tail i), f n_1) =
          (∑ n_1 ∈ Finset.Ico offset
            (offset + (rowDegree 0 + ∑ i : Fin n, tail i)), f n_1) := by
        have hmn : offset ≤ offset + rowDegree 0 := by omega
        have hnk :
            offset + rowDegree 0 ≤
              (offset + rowDegree 0) + ∑ i : Fin n, tail i := by omega
        have h := Finset.sum_Ico_consecutive f hmn hnk
        simpa [Nat.add_assoc] using h
      calc
        (∑ i : Fin (n + 1),
          if k ∈ uniformColumnDegreeShiftedCellSet hcols offset
            rowDegree i then 1 else 0)
            = (if k ∈ uniformColumnDegreeShiftedCellSet hcols offset
                  rowDegree 0 then 1 else 0) +
                (∑ i : Fin n,
                  if k ∈ uniformColumnDegreeShiftedCellSet hcols offset
                    rowDegree i.succ then 1 else 0) := by
                rw [Fin.sum_univ_succ]
        _ = (if k ∈ uniformColumnDegreeIntervalCellSet hcols offset
                  (rowDegree 0) then 1 else 0) +
                (∑ i : Fin n,
                  if k ∈ uniformColumnDegreeShiftedCellSet hcols
                    (offset + rowDegree 0) tail i then 1 else 0) := by
                rw [htailSet]
                have hprefix0 : uniformColumnDegreePrefix rowDegree 0 = 0 := by
                  unfold uniformColumnDegreePrefix
                  simp
                simp [uniformColumnDegreeShiftedCellSet,
                  uniformColumnDegreeIntervalCellSet,
                  uniformColumnDegreeIntervalCellMap, hprefix0]
        _ = (∑ n_1 ∈ Finset.Ico offset (offset + rowDegree 0), f n_1) +
                (∑ n_1 ∈ Finset.Ico (offset + rowDegree 0)
                  ((offset + rowDegree 0) + ∑ i : Fin n, tail i), f n_1) := by
                rw [hfirst]
                rw [htail]
        _ = (∑ n_1 ∈ Finset.Ico offset
              (offset + (rowDegree 0 + ∑ i : Fin n, tail i)), f n_1) :=
                hcombine
        _ = (∑ n_1 ∈ Finset.Ico offset
              (offset + ∑ i : Fin (n + 1), rowDegree i), f n_1) := by
                rw [hsumRows]

theorem uniformColumnDegreeIntervalPartitionGoal :
    UniformColumnDegreeIntervalPartitionGoal := by
  intro rows cols rowDegree hcols hrowLe k
  have h := uniformColumnDegreeShiftedIntervalPartition
    rowDegree hcols hrowLe 0 k
  simpa [uniformColumnDegreeShiftedCellSet,
    uniformColumnDegreeIntervalCellSet,
    uniformColumnDegreeIntervalCellMap,
    uniformColumnDegreeCellSet, uniformColumnDegreeCellMap] using h

theorem uniformColumnDegreeBlockResidueSum
    (cols h : Nat) (k : Fin cols) :
    (∑ n ∈ Finset.Ico (h * cols) (h * cols + cols),
      if n % cols = k.val then (1 : Nat) else 0) = 1 := by
  have hfilter :
      (Finset.Ico (h * cols) (h * cols + cols)).filter
        (fun n => n % cols = k.val) = {h * cols + k.val} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · intro hn
      rcases hn with ⟨⟨hle, hlt⟩, hmod⟩
      have htlt : n - h * cols < cols := by omega
      have hn' : n = h * cols + (n - h * cols) := by omega
      have hmodt : n % cols = n - h * cols := by
        calc
          n % cols = (h * cols + (n - h * cols)) % cols := by
            conv_lhs => rw [hn']
          _ = (n - h * cols) % cols := by rw [Nat.mul_add_mod_self_right]
          _ = n - h * cols := Nat.mod_eq_of_lt htlt
      omega
    · intro hn
      subst n
      constructor
      · constructor <;> omega
      · rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt k.is_lt]
  rw [← Finset.card_filter, hfilter]
  simp

theorem uniformColumnDegreeRangeResidueSum_mul
    (cols h : Nat) (hcols : 0 < cols) (k : Fin cols) :
    (∑ n ∈ Finset.range (h * cols),
      if n % cols = k.val then (1 : Nat) else 0) = h := by
  induction h with
  | zero => simp
  | succ h ih =>
      let f : Nat → Nat := fun n => if n % cols = k.val then 1 else 0
      have hle : h * cols ≤ (h + 1) * cols := by nlinarith [hcols]
      have hsplit := Finset.sum_range_add_sum_Ico (f := f) hle
      have hblock :
          (∑ n ∈ Finset.Ico (h * cols) ((h + 1) * cols), f n) = 1 := by
        have htop : (h + 1) * cols = h * cols + cols := by ring
        rw [htop]
        exact uniformColumnDegreeBlockResidueSum cols h k
      have hgoal : (∑ n ∈ Finset.range ((h + 1) * cols), f n) = h + 1 := by
        rw [← hsplit]
        rw [ih, hblock]
      simpa [f] using hgoal

theorem uniformColumnDegreeResidueCountGoal_of_intervalPartition
    (hPartition : UniformColumnDegreeIntervalPartitionGoal) :
    UniformColumnDegreeResidueCountGoal := by
  intro rows cols h rowDegree hcols hrowLe htotal k
  rw [hPartition rowDegree hcols hrowLe k, htotal]
  exact uniformColumnDegreeRangeResidueSum_mul cols h hcols k

theorem uniformColumnDegreeCellMap_injective {rows cols : Nat}
    (hcols : 0 < cols) (rowDegree : Fin rows → Nat)
    (hrowLe : ∀ i : Fin rows, rowDegree i ≤ cols) (i : Fin rows) :
    Function.Injective (uniformColumnDegreeCellMap hcols rowDegree i) := by
  intro a b hab
  apply Fin.ext
  have hval :
      (uniformColumnDegreePrefix rowDegree i + a.val) % cols =
        (uniformColumnDegreePrefix rowDegree i + b.val) % cols := by
    exact congrArg Fin.val hab
  have hmod :
      uniformColumnDegreePrefix rowDegree i + a.val ≡
        uniformColumnDegreePrefix rowDegree i + b.val [MOD cols] := hval
  have habmod : a.val ≡ b.val [MOD cols] :=
    Nat.ModEq.add_left_cancel'
      (uniformColumnDegreePrefix rowDegree i) hmod
  exact Nat.ModEq.eq_of_lt_of_lt habmod
    (lt_of_lt_of_le a.is_lt (hrowLe i))
    (lt_of_lt_of_le b.is_lt (hrowLe i))

theorem uniformColumnDegreeMatrix_row_sum {rows cols : Nat}
    (hcols : 0 < cols) (rowDegree : Fin rows → Nat)
    (hrowLe : ∀ i : Fin rows, rowDegree i ≤ cols) (i : Fin rows) :
    (∑ k : Fin cols, uniformColumnDegreeMatrix hcols rowDegree i k) =
      rowDegree i := by
  let S : Finset (Fin cols) := uniformColumnDegreeCellSet hcols rowDegree i
  have hsum :
      (∑ k : Fin cols, uniformColumnDegreeMatrix hcols rowDegree i k) =
        (Finset.univ.filter (fun k : Fin cols => k ∈ S)).card := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro k _hk
    simp [uniformColumnDegreeMatrix, S]
  have hfilter :
      (Finset.univ.filter (fun k : Fin cols => k ∈ S)) = S := by
    ext k
    simp [S]
  have hcardS :
      S.card = Fintype.card (Fin (rowDegree i)) := by
    dsimp [S, uniformColumnDegreeCellSet]
    exact Finset.card_image_of_injective
      (Finset.univ : Finset (Fin (rowDegree i)))
      (uniformColumnDegreeCellMap_injective hcols rowDegree hrowLe i)
  calc
    (∑ k : Fin cols, uniformColumnDegreeMatrix hcols rowDegree i k)
        = (Finset.univ.filter (fun k : Fin cols => k ∈ S)).card := hsum
    _ = S.card := by rw [hfilter]
    _ = rowDegree i := by
      rw [hcardS]
      exact Fintype.card_fin (rowDegree i)

theorem uniformColumnDegreeMatrixGoal_of_residueCount
    (hResidue : UniformColumnDegreeResidueCountGoal) :
    UniformColumnDegreeMatrixGoal := by
  intro rows cols h rowDegree hcols hrowLe htotal
  exact ⟨{
    G := uniformColumnDegreeMatrix hcols rowDegree
    G_zero_one := by
      intro i k
      unfold uniformColumnDegreeMatrix
      by_cases hk : k ∈ uniformColumnDegreeCellSet hcols rowDegree i
      · simp [hk]
      · simp [hk]
    G_row_sum := uniformColumnDegreeMatrix_row_sum hcols rowDegree hrowLe
    G_col_sum := by
      intro k
      exact hResidue rowDegree hcols hrowLe htotal k
  }⟩

theorem uniformColumnDegreeMatrixGoal :
    UniformColumnDegreeMatrixGoal :=
  uniformColumnDegreeMatrixGoal_of_residueCount
    (uniformColumnDegreeResidueCountGoal_of_intervalPartition
      uniformColumnDegreeIntervalPartitionGoal)

def OrdinaryQeq1AuxDegreeArithmeticGoal : Prop :=
  ∀ {n r : Nat},
    Odd (n + 1) → 5 ≤ n + 1 →
    Odd (n + r) →
    r < n → 0 < r →
    0 < n - 1 ∧
    (∀ i : Fin n, ordinaryQeq1AuxDegree n r i ≤ n - 1) ∧
    (∑ i : Fin n, ordinaryQeq1AuxDegree n r i) =
      ((n - 2) / 2) * (n - 1)

def OrdinaryQeq1AuxDegreeTotalGoal : Prop :=
  ∀ {n r : Nat},
    Odd (n + 1) → 5 ≤ n + 1 →
    Odd (n + r) →
    r < n → 0 < r →
    (∑ i : Fin n, ordinaryQeq1AuxDegree n r i) =
      ((n - 2) / 2) * (n - 1)

theorem ordinaryQeq1AuxDegreeTotalGoal :
    OrdinaryQeq1AuxDegreeTotalGoal := by
  intro n r hdodd _hd5 hmodd hrlt hrpos
  have hrodd : Odd r :=
    OrdinaryQeq1AuxDegreeMatrixData.odd_r_of_odd_n_add_one_and_odd_n_add_r
      hdodd hmodd
  have hsumRNat :
      (∑ i : Fin n, if i.val < r then (1 : Nat) else 0) = r := by
    rw [sum_fin_indicator_val_lt]
    omega
  have hsumRPredNat :
      (∑ i : Fin n, if i.val < r - 1 then (1 : Nat) else 0) = r - 1 := by
    rw [sum_fin_indicator_val_lt]
    omega
  have hsumR :
      (∑ i : Fin n, if i.val < r then (1 : Int) else 0) = (r : Int) := by
    exact_mod_cast hsumRNat
  have hsumRPred :
      (∑ i : Fin n, if i.val < r - 1 then (1 : Int) else 0) =
        (r - 1 : Nat) := by
    exact_mod_cast hsumRPredNat
  have hInt :
      (∑ i : Fin n, (ordinaryQeq1AuxDegree n r i : Int)) =
        (((n - 2) / 2) * (n - 1) : Nat) := by
    let A : Int := ((r - 3) / 2 : Nat)
    let B : Int := ((r - 1) / 2 : Nat)
    let C : Int := ((n + r - 3) / 2 : Nat)
    have hpoint : ∀ i : Fin n,
        (ordinaryQeq1AuxDegree n r i : Int) =
          C
            + (B - C) * (if i.val < r then (1 : Int) else 0)
            + (A - B) * (if i.val < r - 1 then (1 : Int) else 0) := by
      intro i
      unfold ordinaryQeq1AuxDegree
      by_cases hlow : i.val < r - 1
      · have hmid : i.val < r := by omega
        simp only [hlow, hmid, ↓reduceIte, A, B, C]
        ring
      · by_cases hmid : i.val < r
        · simp only [hlow, hmid, ↓reduceIte, A, B, C]
          ring
        · simp only [hlow, hmid, ↓reduceIte, A, B, C]
          ring
    have hsumRBC :
        (∑ x : Fin n, if x.val < r then B - C else 0) =
          (B - C) * (r : Int) := by
      calc
        (∑ x : Fin n, if x.val < r then B - C else 0)
            = (B - C) *
                (∑ x : Fin n, if x.val < r then (1 : Int) else 0) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro x _hx
                by_cases hxlt : x.val < r <;> simp [hxlt]
        _ = (B - C) * (r : Int) := by rw [hsumR]
    have hsumRPredAB :
        (∑ x : Fin n, if x.val < r - 1 then A - B else 0) =
          (A - B) * ((r - 1 : Nat) : Int) := by
      calc
        (∑ x : Fin n, if x.val < r - 1 then A - B else 0)
            = (A - B) *
                (∑ x : Fin n, if x.val < r - 1 then (1 : Int) else 0) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro x _hx
                by_cases hxlt : x.val < r - 1 <;> simp [hxlt]
        _ = (A - B) * ((r - 1 : Nat) : Int) := by rw [hsumRPred]
    calc
      (∑ i : Fin n, (ordinaryQeq1AuxDegree n r i : Int))
          = ∑ i : Fin n,
              (C
                + (B - C) * (if i.val < r then (1 : Int) else 0)
                + (A - B) * (if i.val < r - 1 then (1 : Int) else 0)) := by
              apply Finset.sum_congr rfl
              intro i _hi
              exact hpoint i
      _ =
          (n : Int) * C + (B - C) * (r : Int)
            + (A - B) * ((r - 1 : Nat) : Int) := by
              simp [Finset.sum_add_distrib, hsumRBC, hsumRPredAB,
                Fintype.card_fin]
      _ = (((n - 2) / 2) * (n - 1) : Nat) := by
              rcases hdodd with ⟨a, ha⟩
              rcases hrodd with ⟨s, hs⟩
              have hn : n = 2 * a := by omega
              have hr : r = 2 * s + 1 := by omega
              subst n
              subst r
              by_cases hs0 : s = 0
              · subst s
                have hC : ((2 * a + 1 - 3) / 2 : Nat) = a - 1 := by omega
                have hR : ((2 * a - 2) / 2 : Nat) = a - 1 := by omega
                have hAint : A = 0 := by simp [A]
                have hBint : B = 0 := by simp [B]
                have hCint : C = ((a - 1 : Nat) : Int) := by
                  change (((2 * a + 1 - 3) / 2 : Nat) : Int) =
                    ((a - 1 : Nat) : Int)
                  exact_mod_cast hC
                rw [hAint, hBint, hCint, hR]
                have ha2 : 2 ≤ a := by omega
                have hcastPred : ((a - 1 : Nat) : Int) = (a : Int) - 1 := by
                  omega
                have hcastTop :
                    ((2 * a - 1 : Nat) : Int) = (2 : Int) * a - 1 := by
                  omega
                simp only [Nat.cast_mul, Nat.cast_ofNat, zero_sub, mul_zero,
                  zero_add, Nat.cast_one, mul_one, sub_self, tsub_self,
                  CharP.cast_eq_zero, add_zero, hcastPred]
                rw [hcastTop]
                ring
              · have hspos : 1 ≤ s := by omega
                have hA : ((2 * s + 1 - 3) / 2 : Nat) = s - 1 := by omega
                have hB : ((2 * s + 1 - 1) / 2 : Nat) = s := by omega
                have hC :
                    ((2 * a + (2 * s + 1) - 3) / 2 : Nat) =
                      a + s - 1 := by omega
                have hR : ((2 * a - 2) / 2 : Nat) = a - 1 := by omega
                have hAint : A = ((s - 1 : Nat) : Int) := by
                  change (((2 * s + 1 - 3) / 2 : Nat) : Int) =
                    ((s - 1 : Nat) : Int)
                  exact_mod_cast hA
                have hBint : B = (s : Int) := by
                  change (((2 * s + 1 - 1) / 2 : Nat) : Int) = (s : Int)
                  exact_mod_cast hB
                have hCint : C = ((a + s - 1 : Nat) : Int) := by
                  change (((2 * a + (2 * s + 1) - 3) / 2 : Nat) : Int) =
                    ((a + s - 1 : Nat) : Int)
                  exact_mod_cast hC
                rw [hAint, hBint, hCint, hR]
                have ha1 : 1 ≤ a := by omega
                have hcastSPred :
                    ((s - 1 : Nat) : Int) = (s : Int) - 1 := by
                  omega
                have hcastASPred :
                    ((a + s - 1 : Nat) : Int) = (a : Int) + (s : Int) - 1 := by
                  omega
                have hcastAPred :
                    ((a - 1 : Nat) : Int) = (a : Int) - 1 := by
                  omega
                have hcastTop :
                    ((2 * a - 1 : Nat) : Int) = (2 : Int) * a - 1 := by
                  omega
                have hcastDoubleA : ((2 * a : Nat) : Int) = (2 : Int) * a := by
                  omega
                have hcastDoubleSPlus :
                    ((2 * s + 1 : Nat) : Int) = (2 : Int) * s + 1 := by
                  omega
                simp [Nat.cast_mul, hcastSPred, hcastASPred, hcastAPred,
                  hcastTop, hcastDoubleA, hcastDoubleSPlus]
                ring
  exact_mod_cast hInt

def OrdinaryQeq1AuxMatrixGoal : Prop :=
  ∀ {n r : Nat},
    Odd (n + 1) → 5 ≤ n + 1 →
    Odd (n + r) →
    r < n → 0 < r →
    Nonempty (OrdinaryQeq1AuxMatrixData n r)

def OrdinaryQeq1SpecialMatchingGoal : Prop :=
  ∀ {n r : Nat} (A : OrdinaryQeq1AuxMatrixData n r),
    Odd (n + 1) → 5 ≤ n + 1 →
    Odd (n + r) →
    r < n → 0 < r →
    Nonempty (OrdinaryQeq1SpecialMatchingData A)

def OrdinaryQeq1AuxSpecialMatchingDataGoal : Prop :=
  ∀ {n r : Nat},
    Odd (n + 1) → 5 ≤ n + 1 →
    Odd (n + r) →
    r < n → 0 < r →
    Nonempty (OrdinaryQeq1AuxSpecialMatchingData n r)

def OrdinaryQeq1AuxPRowSpecialMatchingDataGoal : Prop :=
  ∀ {n r : Nat},
    Odd (n + 1) → 5 ≤ n + 1 →
    Odd (n + r) →
    r < n → 0 < r →
    Nonempty (OrdinaryQeq1AuxPRowSpecialMatchingData n r)

def OrdinaryQeq1DegreeSpecialMatchingGoal : Prop :=
  ∀ {n r : Nat}
    (hdodd : Odd (n + 1)) (_hd5 : 5 ≤ n + 1)
    (hmodd : Odd (n + r)) (_hrlt : r < n) (_hrpos : 0 < r)
    (G : OrdinaryQeq1AuxDegreeMatrixData n r),
    Nonempty (OrdinaryQeq1SpecialMatchingData
      (G.toAuxMatrixData hdodd hmodd))

namespace OrdinaryQeq1SpecialMatchingCounterexample

def B (i : Fin 8) (k : Fin 7) : Int :=
  if (i.val = 0 ∧ k.val = 5) ∨
     (i.val = 1 ∧ k.val = 6) ∨
     (i.val = 2 ∧ k.val = 5) ∨
     (i.val = 3 ∧ k.val = 5) ∨
     (i.val = 4 ∧ (k.val = 1 ∨ k.val = 3)) ∨
     (i.val = 5 ∧ k.val < 5) ∨
     (i.val = 6 ∧
       (k.val = 0 ∨ k.val = 2 ∨ k.val = 3 ∨ k.val = 4 ∨ k.val = 6)) ∨
     (i.val = 7 ∧
       (k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 4 ∨ k.val = 6))
  then 1 else -1

def aux : OrdinaryQeq1AuxMatrixData 8 5 where
  B := B
  B_pm_one := by
    intro i k
    unfold B
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  B_row_sum := by
    intro i
    fin_cases i <;> decide
  B_col_sum := by
    intro k
    fin_cases k <;> decide

def degree : OrdinaryQeq1AuxDegreeMatrixData 8 5 where
  G := fun i k => if B i k = 1 then 1 else 0
  G_zero_one := by
    intro i k
    by_cases h : B i k = 1 <;> simp [h]
  G_row_sum := by
    intro i
    fin_cases i <;> decide
  G_col_sum := by
    intro k
    fin_cases k <;> decide

theorem no_specialMatching :
    ¬ Nonempty (OrdinaryQeq1SpecialMatchingData aux) := by
  rintro ⟨M⟩
  let col5 : Fin 7 := ⟨5, by decide⟩
  have hnot : ∀ i : Fin 8, ¬ (5 ≤ i.val ∧ M.mate i = col5) := by
    intro i hi
    have hp := M.mate_pos i hi.1
    rw [hi.2] at hp
    fin_cases i <;> simp at hi
    all_goals norm_num [aux, B] at hp
  have hcol := M.mate_col_sum col5
  have hzero :
      (∑ i : Fin 8,
        if 5 ≤ i.val ∧ M.mate i = col5 then (1 : Int) else 0) = 0 := by
    simp [hnot]
  have hone :
      (if col5.val < 5 then
          if col5 = M.mate M.special then (1 : Int) else 0
        else 1) = 1 := by
    simp [col5]
  rw [hzero, hone] at hcol
  norm_num at hcol

theorem no_degreeSpecialMatching :
    ¬ Nonempty (OrdinaryQeq1SpecialMatchingData
      (degree.toAuxMatrixData (by decide) (by decide))) := by
  rintro ⟨M⟩
  let col5 : Fin 7 := ⟨5, by decide⟩
  have hnot : ∀ i : Fin 8, ¬ (5 ≤ i.val ∧ M.mate i = col5) := by
    intro i hi
    have hp := M.mate_pos i hi.1
    rw [hi.2] at hp
    fin_cases i <;> simp at hi
    all_goals
      norm_num [degree, B, OrdinaryQeq1AuxDegreeMatrixData.toAuxMatrixData]
        at hp
    all_goals
      have hpval := congrArg Fin.val hp
      norm_num [col5] at hpval
  have hcol := M.mate_col_sum col5
  have hzero :
      (∑ i : Fin 8,
        if 5 ≤ i.val ∧ M.mate i = col5 then (1 : Int) else 0) = 0 := by
    simp [hnot]
  have hone :
      (if col5.val < 5 then
          if col5 = M.mate M.special then (1 : Int) else 0
        else 1) = 1 := by
    simp [col5]
  rw [hzero, hone] at hcol
  norm_num at hcol

end OrdinaryQeq1SpecialMatchingCounterexample

theorem not_ordinaryQeq1SpecialMatchingGoal :
    ¬ OrdinaryQeq1SpecialMatchingGoal := by
  intro h
  exact OrdinaryQeq1SpecialMatchingCounterexample.no_specialMatching
    (h OrdinaryQeq1SpecialMatchingCounterexample.aux
      (by decide) (by decide) (by decide) (by decide) (by decide))

theorem not_ordinaryQeq1DegreeSpecialMatchingGoal :
    ¬ OrdinaryQeq1DegreeSpecialMatchingGoal := by
  intro h
  exact OrdinaryQeq1SpecialMatchingCounterexample.no_degreeSpecialMatching
    (h (by decide) (by decide) (by decide) (by decide) (by decide)
      OrdinaryQeq1SpecialMatchingCounterexample.degree)

theorem ordinaryQeq1AuxMatrixGoal_of_degreeMatrix
    (hDegree : OrdinaryQeq1AuxDegreeMatrixGoal) :
    OrdinaryQeq1AuxMatrixGoal := by
  intro n r hdodd hd5 hmodd hrlt hrpos
  rcases hDegree hdodd hd5 hmodd hrlt hrpos with ⟨G⟩
  exact ⟨G.toAuxMatrixData hdodd hmodd⟩

theorem ordinaryQeq1AuxDegreeMatrixGoal_of_uniformColumnDegree
    (hArith : OrdinaryQeq1AuxDegreeArithmeticGoal)
    (hUniform : UniformColumnDegreeMatrixGoal) :
    OrdinaryQeq1AuxDegreeMatrixGoal := by
  intro n r hdodd hd5 hmodd hrlt hrpos
  rcases hArith hdodd hd5 hmodd hrlt hrpos with
    ⟨hcols, hrowLe, htotal⟩
  rcases hUniform
      (ordinaryQeq1AuxDegree n r)
      hcols hrowLe htotal with
    ⟨M⟩
  exact ⟨M.toOrdinaryQeq1AuxDegreeMatrixData⟩

theorem ordinaryQeq1AuxSpecialMatchingDataGoal_of_degreeMatrix_and_degreeSpecialMatching
    (hDegree : OrdinaryQeq1AuxDegreeMatrixGoal)
    (hMatch : OrdinaryQeq1DegreeSpecialMatchingGoal) :
    OrdinaryQeq1AuxSpecialMatchingDataGoal := by
  intro n r hdodd hd5 hmodd hrlt hrpos
  rcases hDegree hdodd hd5 hmodd hrlt hrpos with ⟨G⟩
  rcases hMatch hdodd hd5 hmodd hrlt hrpos G with ⟨M⟩
  exact ⟨{
    aux := G.toAuxMatrixData hdodd hmodd
    matching := M
  }⟩

theorem ordinaryQeq1AuxSpecialMatchingDataGoal_of_pRowSpecialMatchingData
    (hData : OrdinaryQeq1AuxPRowSpecialMatchingDataGoal) :
    OrdinaryQeq1AuxSpecialMatchingDataGoal := by
  intro n r hdodd hd5 hmodd hrlt hrpos
  rcases hData hdodd hd5 hmodd hrlt hrpos with ⟨D⟩
  exact ⟨D.toAuxSpecialMatchingData⟩

theorem ordinaryQeq1AuxDegreeArithmeticGoal_of_total
    (hTotal : OrdinaryQeq1AuxDegreeTotalGoal) :
    OrdinaryQeq1AuxDegreeArithmeticGoal := by
  intro n r hdodd hd5 hmodd hrlt hrpos
  refine ⟨by omega, ?_, hTotal hdodd hd5 hmodd hrlt hrpos⟩
  intro i
  unfold ordinaryQeq1AuxDegree
  by_cases hlow : i.val < r - 1
  · simp only [hlow, ↓reduceIte]
    rw [Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2)]
    omega
  · by_cases hmid : i.val < r
    · simp only [hlow, hmid, ↓reduceIte]
      rw [Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2)]
      omega
    · simp only [hlow, hmid, ↓reduceIte]
      rw [Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2)]
      omega

theorem ordinaryQeq1AuxDegreeMatrixGoal :
    OrdinaryQeq1AuxDegreeMatrixGoal :=
  ordinaryQeq1AuxDegreeMatrixGoal_of_uniformColumnDegree
    (ordinaryQeq1AuxDegreeArithmeticGoal_of_total
      ordinaryQeq1AuxDegreeTotalGoal)
    uniformColumnDegreeMatrixGoal

theorem ordinaryQeq1AuxSpecialMatchingDataGoal_of_degreeSpecialMatching
    (hMatch : OrdinaryQeq1DegreeSpecialMatchingGoal) :
    OrdinaryQeq1AuxSpecialMatchingDataGoal :=
  ordinaryQeq1AuxSpecialMatchingDataGoal_of_degreeMatrix_and_degreeSpecialMatching
    ordinaryQeq1AuxDegreeMatrixGoal hMatch

def OrdinaryQeq1CanonicalCorrectionDataGoal : Prop :=
  ∀ {n r : Nat},
    Odd (n + 1) → 5 ≤ n + 1 →
    Odd (n + r) →
    r < n → 0 < r →
    Nonempty (OrdinaryQeq1CanonicalCorrectionData n r)

theorem ordinaryQeq1CanonicalCorrectionDataGoal_of_auxMatrix_and_specialMatching
    (hAux : OrdinaryQeq1AuxMatrixGoal)
    (hMatch : OrdinaryQeq1SpecialMatchingGoal) :
    OrdinaryQeq1CanonicalCorrectionDataGoal := by
  intro n r hdodd hd5 hmodd hrlt hrpos
  rcases hAux hdodd hd5 hmodd hrlt hrpos with ⟨A⟩
  rcases hMatch A hdodd hd5 hmodd hrlt hrpos with ⟨M⟩
  exact ⟨M.toCorrectionData⟩

theorem ordinaryQeq1CanonicalCorrectionDataGoal_of_auxSpecialMatchingData
    (hData : OrdinaryQeq1AuxSpecialMatchingDataGoal) :
    OrdinaryQeq1CanonicalCorrectionDataGoal := by
  intro n r hdodd hd5 hmodd hrlt hrpos
  rcases hData hdodd hd5 hmodd hrlt hrpos with ⟨D⟩
  exact ⟨D.toCorrectionData⟩

def OrdinaryQeq1CanonicalMatrixGoal : Prop :=
  ∀ {n m r : Nat},
    Odd (n + 1) → 5 ≤ n + 1 → Odd m →
    m = n + r →
    r < n → 0 < r →
    Nonempty (OrdinaryQeq1CanonicalMatrixData n m r)

def OrdinaryQeq1CanonicalCorrectionGoal : Prop :=
  ∀ {n r : Nat},
    Odd (n + 1) → 5 ≤ n + 1 →
    Odd (n + r) →
    r < n → 0 < r →
    Nonempty (OrdinaryQeq1CanonicalMatrixData n (n + r) r)

theorem ordinaryQeq1CanonicalCorrectionGoal_of_dataGoal
    (hData : OrdinaryQeq1CanonicalCorrectionDataGoal) :
    OrdinaryQeq1CanonicalCorrectionGoal := by
  intro n r hdodd hd5 hmodd hrlt hrpos
  rcases hData hdodd hd5 hmodd hrlt hrpos with ⟨D⟩
  exact ⟨D.toCanonicalMatrixData hrlt hrpos⟩

theorem ordinaryQeq1CanonicalMatrixGoal_of_correction
    (hCorrection : OrdinaryQeq1CanonicalCorrectionGoal) :
    OrdinaryQeq1CanonicalMatrixGoal := by
  intro n m r hdodd hd5 hmodd hmnr hrlt hrpos
  subst m
  rcases hCorrection hdodd hd5 hmodd hrlt hrpos with ⟨M⟩
  exact ⟨M⟩

theorem ordinaryQeq1SignedCoreGoal_of_canonicalMatrix
    (hMatrix : OrdinaryQeq1CanonicalMatrixGoal) :
    OrdinaryQeq1SignedCoreGoal := by
  intro n m r hdodd hd5 hmodd hmnr hrlt hrpos
  rcases hMatrix hdodd hd5 hmodd hmnr hrlt hrpos with ⟨M⟩
  refine ⟨{
    a := fun i : Fin n => if i.val < r - 1 then 2 else 1
    epsBit := fun i : Fin n => if i.val < r then 1 else 0
    c := fun k : Fin (n - 1) => if k.val < r then 2 else 1
    S := M.S
    a_sum := ?_
    eps_sum := ?_
    c_sum := ?_
    a_one_two := ?_
    eps_zero_one := ?_
    c_one_two := ?_
    S_signed := M.S_signed
    S_ge_neg_one_of_eps_zero := ?_
    S_row_sum := ?_
    S_col_sum := ?_
  }⟩
  · rw [sum_fin_two_one_val_lt]
    have hmin : min n (r - 1) = r - 1 := by omega
    rw [hmin, hmnr]
    omega
  · rw [sum_fin_indicator_val_lt]
    have hmin : min n r = r := by omega
    exact hmin
  · rw [sum_fin_two_one_val_lt]
    have hmin : min (n - 1) r = r := by omega
    rw [hmin, hmnr]
    omega
  · intro i
    by_cases h : i.val < r - 1 <;> simp [h]
  · intro i
    by_cases h : i.val < r <;> simp [h]
  · intro k
    by_cases h : k.val < r <;> simp [h]
  · intro i k heps
    by_cases hlt : i.val < r
    · simp [hlt] at heps
    · exact M.S_ge_neg_one_of_P i k (by omega)
  · intro i
    rw [M.S_row_sum i]
    by_cases hlow : i.val < r - 1
    · have hmid : i.val < r := by omega
      simp [hlow, hmid]
    · by_cases hmid : i.val < r
      · simp [hlow, hmid]
      · simp [hlow, hmid]
  · intro k
    rw [M.S_col_sum k]
    by_cases h : k.val < r <;> simp [h]

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

theorem marginTransportQge2CompatibleGoal_of_ordinaryQge2SignedCore
    (hCore : OrdinaryQge2SignedCoreGoal) :
    MarginTransportQge2CompatibleGoal := by
  intro d m q r hdodd hd5 hmodd hmqr hrlt hrpos hq
  have hd1 : 1 ≤ d := by omega
  have hsucc : d - 1 + 1 = d := Nat.sub_add_cancel hd1
  have hdodd' : Odd (d - 1 + 1) := by
    simpa [hsucc] using hdodd
  have hd5' : 5 ≤ d - 1 + 1 := by
    simpa [hsucc] using hd5
  rcases hCore hdodd' hd5' hmodd hmqr hrlt hrpos hq with ⟨D⟩
  have h :=
    D.marginTransportQge2Compatible_of_ordinaryData hmodd hmqr hq
  rw [hsucc] at h
  exact h

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

theorem marginTransportQeq1CompatibleGoal_of_ordinaryQeq1SignedCore
    (hCore : OrdinaryQeq1SignedCoreGoal) :
    MarginTransportQeq1CompatibleGoal := by
  intro d m q r hdodd hd5 hmodd hmqr hrlt hrpos hq
  subst q
  have hd1 : 1 ≤ d := by omega
  have hsucc : d - 1 + 1 = d := Nat.sub_add_cancel hd1
  have hmnr : m = d - 1 + r := by
    simpa using hmqr
  have hdodd' : Odd (d - 1 + 1) := by
    simpa [hsucc] using hdodd
  have hd5' : 5 ≤ d - 1 + 1 := by
    simpa [hsucc] using hd5
  rcases hCore hdodd' hd5' hmodd hmnr hrlt hrpos with ⟨D⟩
  have h :=
    D.marginTransportQeq1Compatible_of_ordinaryData hmodd hmnr hrpos
  rw [hsucc] at h
  exact h

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

theorem transportQge2Goal_of_compatible
    (hCompat : MarginTransportQge2CompatibleGoal) :
    TransportQge2Goal :=
  transportQge2Goal_of_margin
    (marginTransportQge2Goal_of_compatible hCompat)

theorem transportQeq1Goal_of_compatible
    (hCompat : MarginTransportQeq1CompatibleGoal) :
    TransportQeq1Goal :=
  transportQeq1Goal_of_margin
    (marginTransportQeq1Goal_of_compatible hCompat)

theorem admissiblePartsCountBranchGoal_of_margin
    (hQge2 : MarginTransportQge2Goal)
    (hQeq1 : MarginTransportQeq1Goal) :
    AdmissiblePartsCountBranchGoal :=
  admissiblePartsCountBranchGoal_of_transports
    (transportQge2Goal_of_margin hQge2)
    (transportQeq1Goal_of_margin hQeq1)

theorem admissiblePartsCountBranchGoal_of_compatible
    (hQge2 : MarginTransportQge2CompatibleGoal)
    (hQeq1 : MarginTransportQeq1CompatibleGoal) :
    AdmissiblePartsCountBranchGoal :=
  admissiblePartsCountBranchGoal_of_transports
    (transportQge2Goal_of_compatible hQge2)
    (transportQeq1Goal_of_compatible hQeq1)

end PrefixCount
end RoundComposite
