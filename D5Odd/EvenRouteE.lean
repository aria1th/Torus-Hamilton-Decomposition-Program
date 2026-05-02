import D5Odd.Even
import Shared.Monodromy
import Shared.RankCycle

namespace D5Odd

/-!
Lean-facing interface for the D5 even Route-E track.

The program-side Route-E verifier works with one-`Lambda_E` schedules,
count/slot data, and a small seam of size `m-1`.  This file records the shape
of the certificate that should eventually be produced from those traces.  The
existing endpoint bridge remains `D5EvenSeamReturnOrbitTarget` from
`D5Odd.Even`.
-/

structure RouteECounts (m : Nat) where
  slot : Fin 5
  counts : Fin 5 → Nat
  count_sum : (Finset.univ.sum counts) = m - 1

namespace RouteEB20

/-!
Arithmetic data for the first extracted D5 even Route-E branch.

The branch is `m = 24*q + 20`, slot zero, with count vector
`(r,0,0,h+r,r)` where `h = m/2 = 12*q+10` and `r = (h-1)/3 = 4*q+3`.
The program verifier `scripts/verify_d5_routeE_b20_branch.py` checks the
corresponding first-return and pointwise return-time formulas.  The lemmas
below record the count-sum and return-time weighted-sum arithmetic needed by
the eventual symbolic certificate.
-/

def modulus (q : Nat) : Nat := 24 * q + 20

def half (q : Nat) : Nat := 12 * q + 10

def third (q : Nat) : Nat := 4 * q + 3

def repeatedTimeCount (q : Nat) : Nat := 12 * q + 6

def counts (q : Nat) : Fin 5 → Nat :=
  ![third q, 0, 0, half q + third q, third q]

theorem counts_sum (q : Nat) :
    Finset.univ.sum (counts q) = modulus q - 1 := by
  simp [counts, Fin.sum_univ_five, third, half, modulus]
  omega

def routeCounts (q : Nat) : RouteECounts (modulus q) where
  slot := 0
  counts := counts q
  count_sum := counts_sum q

def timeA (q : Nat) : Nat :=
  13824 * q ^ 3 + 34272 * q ^ 2 + 28320 * q + 7806

def timeC (q : Nat) : Nat :=
  timeA q + modulus q * (modulus q + 1)

def timeE (q : Nat) : Nat :=
  20736 * q ^ 3 + 50976 * q ^ 2 + 41772 * q + 11416

def timeF (q : Nat) : Nat :=
  20736 * q ^ 3 + 51552 * q ^ 2 + 42780 * q + 11862

def returnTimeWeightedSum (q : Nat) : Nat :=
  2 * timeA q +
  repeatedTimeCount q * (timeA q + modulus q) +
  3 * timeC q +
  repeatedTimeCount q * (timeC q + modulus q) +
  timeE q +
  timeF q

theorem repeatedTimeCount_eq_half_sub_four (q : Nat) :
    repeatedTimeCount q = half q - 4 := by
  simp [repeatedTimeCount, half]

theorem three_third_eq_half_sub_one (q : Nat) :
    3 * third q = half q - 1 := by
  simp [third, half]
  ring

theorem returnTimeWeightedSum_eq_modulus_pow_four (q : Nat) :
    returnTimeWeightedSum q = modulus q ^ 4 := by
  simp [returnTimeWeightedSum, timeA, timeC, timeE, timeF,
    repeatedTimeCount, modulus]
  ring

end RouteEB20

def LambdaE (S : Mask5) : Color → Direction :=
  if S = mask5 false false false false false then row5 0 1 2 3 4
  else if S = mask5 true false false false false then row5 0 1 3 2 4
  else if S = mask5 false true false false false then row5 0 1 2 4 3
  else if S = mask5 true true false false false then row5 4 1 3 2 0
  else if S = mask5 false false true false false then row5 4 1 2 3 0
  else if S = mask5 true false true false false then row5 4 1 3 0 2
  else if S = mask5 false true true false false then row5 1 0 2 4 3
  else if S = mask5 true true true false false then row5 1 4 3 0 2
  else if S = mask5 false false false true false then row5 1 0 2 3 4
  else if S = mask5 true false false true false then row5 1 3 0 2 4
  else if S = mask5 false true false true false then row5 3 0 2 4 1
  else if S = mask5 true true false true false then row5 4 0 3 2 1
  else if S = mask5 false false true true false then row5 4 2 1 3 0
  else if S = mask5 true false true true false then row5 4 3 1 2 0
  else if S = mask5 false true true true false then row5 3 2 0 4 1
  else if S = mask5 true true true true false then row5 0 1 2 3 4
  else if S = mask5 false false false false true then row5 0 2 1 3 4
  else if S = mask5 true false false false true then row5 0 2 1 4 3
  else if S = mask5 false true false false true then row5 0 2 4 1 3
  else if S = mask5 true true false false true then row5 3 2 4 1 0
  else if S = mask5 false false true false true then row5 2 4 1 3 0
  else if S = mask5 true false true false true then row5 4 2 1 0 3
  else if S = mask5 false true true false true then row5 2 0 1 4 3
  else if S = mask5 true true true false true then row5 0 1 2 3 4
  else if S = mask5 false false false true true then row5 1 0 3 2 4
  else if S = mask5 true false false true true then row5 1 3 0 4 2
  else if S = mask5 false true false true true then row5 1 0 4 2 3
  else if S = mask5 true true false true true then row5 0 1 2 3 4
  else if S = mask5 false false true true true then row5 2 4 3 1 0
  else if S = mask5 true false true true true then row5 0 1 2 3 4
  else if S = mask5 false true true true true then row5 0 1 2 3 4
  else if S = mask5 true true true true true then row5 0 1 2 3 4
  else row5 0 1 2 3 4

set_option linter.style.nativeDecide false in
theorem LambdaE_latin : ∀ S : Mask5, Function.Bijective (LambdaE S) := by
  native_decide

set_option linter.style.nativeDecide false in
theorem LambdaE_cyclic :
    ∀ (S : Mask5) (a c : Color),
      LambdaE (rotMask c S) (fin5AddNat a c.val) =
        fin5AddNat (LambdaE S a) c.val := by
  native_decide

theorem card_vec4 (m : Nat) [NeZero m] :
    Fintype.card (Vec4 m) = m ^ 4 := by
  calc
    Fintype.card (Vec4 m) = Fintype.card (Fin 4 → ZMod m) := rfl
    _ = Fintype.card (ZMod m) ^ 4 := by
      simp
    _ = m ^ 4 := by
      rw [ZMod.card]

abbrev RouteENonzeroSeam (m : Nat) := { a : ZMod m // a ≠ 0 }

theorem card_routeENonzeroSeam (m : Nat) [NeZero m] :
    Fintype.card (RouteENonzeroSeam m) = m - 1 := by
  change Fintype.card { a : ZMod m // a ≠ 0 } = m - 1
  rw [Fintype.card_subtype]
  have hfilter :
      (Finset.univ.filter fun a : ZMod m => a ≠ 0) =
        Finset.univ.erase (0 : ZMod m) := by
    ext a
    simp
  rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ZMod.card]

namespace RouteENonzeroSeam

def toIndex {m : Nat} [NeZero m] (a : RouteENonzeroSeam m) : Fin (m - 1) :=
  ⟨a.1.val - 1, by
    have hpos : 0 < a.1.val := by
      by_contra hnot
      have hzero : a.1.val = 0 := by omega
      exact a.2 ((ZMod.val_eq_zero a.1).mp hzero)
    have hlt := ZMod.val_lt a.1
    omega⟩

def ofIndex {m : Nat} [NeZero m] (i : Fin (m - 1)) : RouteENonzeroSeam m :=
  ⟨((i.val + 1 : Nat) : ZMod m), by
    exact zmod_nat_ne_zero (m := m) (k := i.val + 1) (by omega) (by omega)⟩

set_option linter.flexible false in
theorem ofIndex_toIndex {m : Nat} [NeZero m] (a : RouteENonzeroSeam m) :
    ofIndex (toIndex a) = a := by
  apply Subtype.ext
  simp [ofIndex, toIndex]
  have hpos : 0 < a.1.val := by
    by_contra hnot
    have hzero : a.1.val = 0 := by omega
    exact a.2 ((ZMod.val_eq_zero a.1).mp hzero)
  have hsub : a.1.val - 1 + 1 = a.1.val :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
  calc
    (((a.1.val - 1 : Nat) : ZMod m) + 1) =
        (((a.1.val - 1 + 1 : Nat) : ZMod m)) := by
      simp [Nat.cast_add]
    _ = ((a.1.val : Nat) : ZMod m) := by rw [hsub]
    _ = a.1 := ZMod.natCast_zmod_val a.1

set_option linter.flexible false in
theorem toIndex_ofIndex {m : Nat} [NeZero m] (i : Fin (m - 1)) :
    toIndex (ofIndex i) = i := by
  apply Fin.ext
  simp [toIndex, ofIndex]
  have hcast : (((i.val : Nat) : ZMod m) + 1) =
      (((i.val + 1 : Nat) : ZMod m)) := by
    simp [Nat.cast_add]
  rw [hcast]
  rw [ZMod.val_natCast_of_lt]
  · omega
  · omega

noncomputable def indexEquiv {m : Nat} [NeZero m] :
    RouteENonzeroSeam m ≃ Fin (m - 1) where
  toFun := toIndex
  invFun := ofIndex
  left_inv := ofIndex_toIndex
  right_inv := toIndex_ofIndex

end RouteENonzeroSeam

namespace RouteEB20

instance modulus_neZero (q : Nat) : NeZero (modulus q) :=
  ⟨by simp [modulus]⟩

instance modulus_pred_neZero (q : Nat) : NeZero (modulus q - 1) :=
  ⟨by simp [modulus]⟩

def seamStep (q : Nat) : Nat := half q + 1

theorem seamStep_lt_modulus_pred (q : Nat) :
    seamStep q < modulus q - 1 := by
  simp [seamStep, half, modulus]
  omega

theorem seamStep_coprime (q : Nat) :
    Nat.Coprime (seamStep q) (modulus q - 1) := by
  rw [seamStep, half, modulus]
  have hN : 24 * q + 20 - 1 = (12 * q + 8) + (12 * q + 11) := by
    omega
  rw [hN]
  rw [Nat.coprime_add_self_right]
  have hA : 12 * q + 11 = 3 + (12 * q + 8) := by
    omega
  rw [hA]
  rw [Nat.coprime_add_self_left]
  have hB : 12 * q + 8 = 2 + (4 * q + 2) * 3 := by
    omega
  rw [hB]
  rw [Nat.coprime_add_mul_right_right]
  norm_num

noncomputable def seamIndexAdd (q : Nat) :
    Fin (modulus q - 1) → Fin (modulus q - 1) :=
  fun i => (finZModEquiv (modulus q - 1)).symm
    ((finZModEquiv (modulus q - 1)) i +
      (seamStep q : ZMod (modulus q - 1)))

set_option linter.flexible false in
theorem seamIndexAdd_val (q : Nat) (i : Fin (modulus q - 1)) :
    (seamIndexAdd q i).val =
      (i.val + seamStep q) % (modulus q - 1) := by
  simp [seamIndexAdd, finZModEquiv]
  rw [ZMod.val_add]
  rw [ZMod.val_natCast_of_lt (show i.val < modulus q - 1 from i.isLt)]
  rw [ZMod.val_natCast_of_lt (seamStep_lt_modulus_pred q)]

theorem seamIndexAdd_single_cycle (q : Nat) :
    IsSingleCycleMap (seamIndexAdd q) := by
  refine Shared.single_cycle_of_equiv_conj
    (e := (finZModEquiv (modulus q - 1)).symm)
    (f := seamIndexAdd q)
    (g := fun x : ZMod (modulus q - 1) =>
      x + (seamStep q : ZMod (modulus q - 1)))
    ?_ ?_
  · exact Shared.zmod_add_single_cycle_of_coprime (seamStep_coprime q)
  · intro x
    simp [seamIndexAdd]

noncomputable def seamMap (q : Nat) :
    RouteENonzeroSeam (modulus q) → RouteENonzeroSeam (modulus q) :=
  fun a => RouteENonzeroSeam.ofIndex
    (seamIndexAdd q (RouteENonzeroSeam.toIndex a))

theorem seamMap_single_cycle (q : Nat) :
    IsSingleCycleMap (seamMap q) := by
  refine Shared.single_cycle_of_equiv_conj
    (e := (RouteENonzeroSeam.indexEquiv (m := modulus q)).symm)
    (f := seamMap q)
    (g := seamIndexAdd q)
    (seamIndexAdd_single_cycle q) ?_
  intro i
  change RouteENonzeroSeam.toIndex
      (seamMap q (RouteENonzeroSeam.ofIndex i)) =
    seamIndexAdd q i
  simp [seamMap, RouteENonzeroSeam.toIndex_ofIndex]

set_option linter.flexible false in
theorem seamMap_lower_translation (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (ha : a.1.val ≤ half q - 2) :
    (seamMap q a).1 = a.1 + (seamStep q : ZMod (modulus q)) := by
  simp [seamMap, RouteENonzeroSeam.ofIndex]
  rw [seamIndexAdd_val]
  simp [RouteENonzeroSeam.toIndex]
  have hpos : 0 < a.1.val := by
    by_contra hnot
    have hzero : a.1.val = 0 := by omega
    exact a.2 ((ZMod.val_eq_zero a.1).mp hzero)
  have hlt : a.1.val - 1 + seamStep q < modulus q - 1 := by
    simp [seamStep, half, modulus] at ha ⊢
    omega
  rw [Nat.mod_eq_of_lt hlt]
  have hsub : a.1.val - 1 + seamStep q + 1 =
      a.1.val + seamStep q := by
    simp [seamStep]
    omega
  calc
    (((a.1.val - 1 + seamStep q : Nat) : ZMod (modulus q)) + 1) =
        (((a.1.val - 1 + seamStep q + 1 : Nat) :
          ZMod (modulus q))) := by
      simp [Nat.cast_add]
    _ = (((a.1.val + seamStep q : Nat) : ZMod (modulus q))) := by
      rw [hsub]
    _ = ((a.1.val : Nat) : ZMod (modulus q)) +
        (seamStep q : ZMod (modulus q)) := by
      simp [Nat.cast_add]
    _ = a.1 + (seamStep q : ZMod (modulus q)) := by
      rw [ZMod.natCast_zmod_val a.1]

set_option linter.flexible false in
theorem seamMap_upper_translation (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (ha : half q - 1 ≤ a.1.val) :
    (seamMap q a).1 =
      a.1 + ((seamStep q + 1 : Nat) : ZMod (modulus q)) := by
  simp [seamMap, RouteENonzeroSeam.ofIndex]
  rw [seamIndexAdd_val]
  simp [RouteENonzeroSeam.toIndex]
  have hpos : 0 < a.1.val := by
    by_contra hnot
    have hzero : a.1.val = 0 := by omega
    exact a.2 ((ZMod.val_eq_zero a.1).mp hzero)
  let N := modulus q - 1
  let s := a.1.val - 1 + seamStep q
  have hge : N ≤ s := by
    simp [N, s, seamStep, half, modulus] at ha ⊢
    omega
  have hlt : s - N < N := by
    have aval_lt := ZMod.val_lt a.1
    simp [N, s, seamStep, half, modulus] at ha aval_lt ⊢
    omega
  have hs : s = N + (s - N) := by
    omega
  have hmod : (a.1.val - 1 + seamStep q) %
      (modulus q - 1) = s - N := by
    change s % N = s - N
    rw [hs, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]
    omega
  rw [hmod]
  have hsum : s - N + 1 + modulus q =
      a.1.val + seamStep q + 1 := by
    dsimp [s, N]
    omega
  calc
    (((s - N : Nat) : ZMod (modulus q)) + 1) =
        (((s - N + 1 : Nat) : ZMod (modulus q))) := by
      simp [Nat.cast_add]
    _ = (((s - N + 1 + modulus q : Nat) : ZMod (modulus q))) := by
      simp [Nat.cast_add]
    _ = (((a.1.val + seamStep q + 1 : Nat) :
        ZMod (modulus q))) := by
      rw [hsum]
    _ = ((a.1.val : Nat) : ZMod (modulus q)) +
        (seamStep q : ZMod (modulus q)) + 1 := by
      simp [Nat.cast_add]
    _ = a.1 + (seamStep q : ZMod (modulus q)) + 1 := by
      rw [ZMod.natCast_zmod_val a.1]
    _ = a.1 + ((seamStep q : ZMod (modulus q)) + 1) := by
      ring

end RouteEB20

structure RouteESeamTranslationBlock (m : Nat) where
  start : Nat
  stop : Nat
  delta : ZMod m
  start_pos : 0 < start
  stop_lt : stop < m
  start_le_stop : start ≤ stop

namespace RouteESeamTranslationBlock

def contains {m : Nat} (block : RouteESeamTranslationBlock m)
    (a : RouteENonzeroSeam m) : Prop :=
  block.start ≤ a.1.val ∧ a.1.val ≤ block.stop

def translationFormula {m : Nat} (block : RouteESeamTranslationBlock m)
    (f : RouteENonzeroSeam m → RouteENonzeroSeam m) : Prop :=
  ∀ a, block.contains a → (f a).1 = a.1 + block.delta

end RouteESeamTranslationBlock

namespace RouteEB20

def lowerBlock (q : Nat) : RouteESeamTranslationBlock (modulus q) where
  start := 1
  stop := half q - 2
  delta := (seamStep q : ZMod (modulus q))
  start_pos := by omega
  stop_lt := by
    simp [half, modulus]
    omega
  start_le_stop := by
    simp [half]

def upperBlock (q : Nat) : RouteESeamTranslationBlock (modulus q) where
  start := half q - 1
  stop := modulus q - 1
  delta := ((seamStep q + 1 : Nat) : ZMod (modulus q))
  start_pos := by
    simp [half]
  stop_lt := by
    simp [modulus]
  start_le_stop := by
    simp [half, modulus]
    omega

def seamBlocks (q : Nat) : List (RouteESeamTranslationBlock (modulus q)) :=
  [lowerBlock q, upperBlock q]

theorem seamBlocks_cover (q : Nat)
    (a : RouteENonzeroSeam (modulus q)) :
    ∃ block, block ∈ seamBlocks q ∧ block.contains a := by
  have hpos : 0 < a.1.val := by
    by_contra hnot
    have hzero : a.1.val = 0 := by omega
    exact a.2 ((ZMod.val_eq_zero a.1).mp hzero)
  have hle_last : a.1.val ≤ modulus q - 1 := by
    have hlt := ZMod.val_lt a.1
    omega
  by_cases ha : a.1.val ≤ half q - 2
  · refine ⟨lowerBlock q, ?_, ?_⟩
    · simp [seamBlocks]
    · exact ⟨by simpa [lowerBlock] using Nat.succ_le_of_lt hpos, ha⟩
  · have hupper : half q - 1 ≤ a.1.val := by
      simp [half] at ha ⊢
      omega
    refine ⟨upperBlock q, ?_, ?_⟩
    · simp [seamBlocks]
    · exact ⟨hupper, hle_last⟩

set_option linter.flexible false in
theorem seamBlocks_disjoint (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (block₁ block₂ : RouteESeamTranslationBlock (modulus q)) :
    block₁ ∈ seamBlocks q → block₂ ∈ seamBlocks q →
    block₁.contains a → block₂.contains a → block₁ = block₂ := by
  intro hmem₁ hmem₂ hcontains₁ hcontains₂
  simp [seamBlocks] at hmem₁ hmem₂
  rcases hmem₁ with h₁ | h₁ <;> rcases hmem₂ with h₂ | h₂
  · rw [h₁, h₂]
  · subst block₁
    subst block₂
    exfalso
    simp [RouteESeamTranslationBlock.contains, lowerBlock] at hcontains₁
    simp [RouteESeamTranslationBlock.contains, upperBlock] at hcontains₂
    omega
  · subst block₁
    subst block₂
    exfalso
    simp [RouteESeamTranslationBlock.contains, upperBlock] at hcontains₁
    simp [RouteESeamTranslationBlock.contains, lowerBlock] at hcontains₂
    omega
  · rw [h₁, h₂]

set_option linter.flexible false in
theorem seamBlocks_translation (q : Nat)
    (block : RouteESeamTranslationBlock (modulus q)) :
    block ∈ seamBlocks q →
      block.translationFormula (seamMap q) := by
  intro hmem
  simp [seamBlocks] at hmem
  rcases hmem with hmem | hmem
  · subst block
    intro a hcontains
    exact seamMap_lower_translation q a hcontains.2
  · subst block
    intro a hcontains
    exact seamMap_upper_translation q a hcontains.1

end RouteEB20

def routeEOpenPortFinSquareSucc {m : Nat} (I : Fin m × Fin m) : Fin m × Fin m :=
  (finProdFinEquiv.symm ((finRotate (m * m)) (finProdFinEquiv I)) :
    Fin m × Fin m)

theorem routeEOpenPortFinSquareSucc_single_cycle (m : Nat) :
    IsSingleCycleMap (routeEOpenPortFinSquareSucc (m := m)) := by
  exact single_cycle_of_bijective_semiconj
    (f := finRotate (m * m))
    (g := routeEOpenPortFinSquareSucc (m := m))
    (phi := (finProdFinEquiv.symm : Fin (m * m) → Fin m × Fin m))
    (Equiv.bijective finProdFinEquiv.symm)
    (by
      intro x
      change finProdFinEquiv.symm ((finRotate (m * m)) x) =
        finProdFinEquiv.symm
          ((finRotate (m * m))
            (finProdFinEquiv (finProdFinEquiv.symm x)))
      rw [Equiv.apply_symm_apply])
    (finRotate_single_cycle (m * m))

theorem routeEOpenPortFinSquareSucc_of_col_lt {m : Nat} [NeZero m]
    (I : Fin m × Fin m) (hcol : I.2.val + 1 < m) :
    routeEOpenPortFinSquareSucc I = (I.1, ⟨I.2.val + 1, hcol⟩) := by
  apply (Equiv.injective finProdFinEquiv)
  change finProdFinEquiv
      (finProdFinEquiv.symm ((finRotate (m * m)) (finProdFinEquiv I))) =
    finProdFinEquiv (I.1, ⟨I.2.val + 1, hcol⟩)
  rw [Equiv.apply_symm_apply]
  rw [finRotate_apply]
  apply Fin.ext
  rw [Fin.val_add]
  have hNpos : 0 < m * m := by
    have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    exact Nat.mul_pos hmpos hmpos
  haveI : NeZero (m * m) := ⟨Nat.ne_of_gt hNpos⟩
  have hNgt1 : 1 < m * m := by
    by_cases hm1 : m = 1
    · subst m
      have hbad : I.2.val + 1 < 1 := hcol
      omega
    · have hmge2 : 2 ≤ m := by omega
      nlinarith
  have hone : ((1 : Fin (m * m)).val) = 1 := by
    rw [Fin.coe_ofNat_eq_mod]
    exact Nat.mod_eq_of_lt hNgt1
  rw [hone]
  have hlt : (finProdFinEquiv I).val + 1 < m * m := by
    calc
      (finProdFinEquiv I).val + 1 = I.2.val + m * I.1.val + 1 := by
        simp [finProdFinEquiv]
      _ = (I.2.val + 1) + m * I.1.val := by omega
      _ < m + m * I.1.val := Nat.add_lt_add_right hcol _
      _ = m * (I.1.val + 1) := by rw [Nat.mul_succ, add_comm]
      _ ≤ m * m := Nat.mul_le_mul_left m (Nat.succ_le_of_lt I.1.isLt)
  rw [Nat.mod_eq_of_lt hlt]
  simp [finProdFinEquiv]
  omega

set_option linter.flexible false in
theorem routeEOpenPortFinSquareSucc_of_last_col {m : Nat} [NeZero m]
    (I : Fin m × Fin m) (hcol : I.2.val + 1 = m) :
    routeEOpenPortFinSquareSucc I =
      ((finRotate m) I.1, (⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩ : Fin m)) := by
  by_cases hm1 : m = 1
  · subst m
    rcases I with ⟨i, j⟩
    fin_cases i
    fin_cases j
    rfl
  apply (Equiv.injective finProdFinEquiv)
  change finProdFinEquiv
      (finProdFinEquiv.symm ((finRotate (m * m)) (finProdFinEquiv I))) =
    finProdFinEquiv
      ((finRotate m) I.1, (⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩ : Fin m))
  rw [Equiv.apply_symm_apply]
  by_cases hrow : I.1.val + 1 < m
  · rw [finRotate_of_lt I.1 hrow]
    rw [finRotate_apply]
    apply Fin.ext
    rw [Fin.val_add]
    have hNpos : 0 < m * m := by
      have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
      exact Nat.mul_pos hmpos hmpos
    haveI : NeZero (m * m) := ⟨Nat.ne_of_gt hNpos⟩
    have hNgt1 : 1 < m * m := by
      have hmge2 : 2 ≤ m := by omega
      nlinarith
    have hone : ((1 : Fin (m * m)).val) = 1 := by
      rw [Fin.coe_ofNat_eq_mod]
      exact Nat.mod_eq_of_lt hNgt1
    rw [hone]
    have hlt : (finProdFinEquiv I).val + 1 < m * m := by
      calc
        (finProdFinEquiv I).val + 1 = I.2.val + m * I.1.val + 1 := by
          simp [finProdFinEquiv]
        _ = m * (I.1.val + 1) := by
          rw [Nat.mul_succ]
          omega
        _ < m * m :=
          Nat.mul_lt_mul_of_pos_left hrow (Nat.pos_of_ne_zero (NeZero.ne m))
    rw [Nat.mod_eq_of_lt hlt]
    simp [finProdFinEquiv]
    rw [Nat.mul_succ]
    omega
  · have hroweq : I.1.val + 1 = m := by
      have hle : I.1.val + 1 ≤ m := Nat.succ_le_of_lt I.1.isLt
      omega
    rw [finRotate_of_last I.1 hroweq]
    rw [finRotate_apply]
    apply Fin.ext
    rw [Fin.val_add]
    have hNpos : 0 < m * m := by
      have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
      exact Nat.mul_pos hmpos hmpos
    haveI : NeZero (m * m) := ⟨Nat.ne_of_gt hNpos⟩
    have hNgt1 : 1 < m * m := by
      have hmge2 : 2 ≤ m := by omega
      nlinarith
    have hone : ((1 : Fin (m * m)).val) = 1 := by
      rw [Fin.coe_ofNat_eq_mod]
      exact Nat.mod_eq_of_lt hNgt1
    rw [hone]
    have heqN : (finProdFinEquiv I).val + 1 = m * m := by
      calc
        (finProdFinEquiv I).val + 1 = I.2.val + m * I.1.val + 1 := by
          simp [finProdFinEquiv]
        _ = m * (I.1.val + 1) := by
          rw [Nat.mul_succ]
          omega
        _ = m * m := by rw [hroweq]
    rw [heqN]
    simp [Nat.mod_self, finProdFinEquiv]

theorem finZModEquiv_symm_add_one {m : Nat} [NeZero m] (x : ZMod m) :
    (finZModEquiv m).symm (x + 1) =
      (finRotate m) ((finZModEquiv m).symm x) := by
  apply (Equiv.injective (finZModEquiv m))
  simp [finZModEquiv, finRotate_apply, Fin.val_add]

def routeEOpenPortSectionPairMap {m : Nat}
    (A B : ZMod m) : ZMod m × ZMod m → ZMod m × ZMod m :=
  fun p =>
    if p.1 + p.2 = 0 then
      (p.1 + A, p.2 + B + 1)
    else
      (p.1 + A + 1, p.2 + B)

def routeEOpenPortChart {m : Nat} :
    ZMod m × ZMod m → ZMod m × ZMod m :=
  fun p => (p.1 + p.2, p.1)

def routeEOpenPortChartEquiv {m : Nat} :
    ZMod m × ZMod m ≃ ZMod m × ZMod m where
  toFun := routeEOpenPortChart
  invFun := fun p => (p.2, p.1 - p.2)
  left_inv := by
    intro p
    rcases p with ⟨a, b⟩
    simp [routeEOpenPortChart]
  right_inv := by
    intro p
    rcases p with ⟨sigma, a⟩
    simp [routeEOpenPortChart]

def routeEOpenPortHMap {m : Nat}
    (A C : ZMod m) : ZMod m × ZMod m → ZMod m × ZMod m :=
  fun p => (p.1 - C, p.2 + A + 1 - if p.1 = 0 then 1 else 0)

set_option linter.flexible false in
theorem routeEOpenPortChart_sectionPairMap
    {m : Nat} (A B C : ZMod m)
    (hABC : A + B + C + 1 = 0) (p : ZMod m × ZMod m) :
    routeEOpenPortChart (routeEOpenPortSectionPairMap A B p) =
      routeEOpenPortHMap A C (routeEOpenPortChart p) := by
  rcases p with ⟨a, b⟩
  have hABC' : A + B + 1 = -C := by
    calc
      A + B + 1 = A + B + C + 1 - C := by ring
      _ = 0 - C := by rw [hABC]
      _ = -C := by ring
  by_cases h : a + b = 0
  · apply Prod.ext
    · simp [routeEOpenPortSectionPairMap, routeEOpenPortChart,
        routeEOpenPortHMap, h]
      calc
        a + A + (b + B + 1) = (a + b) + (A + B + 1) := by ring
        _ = 0 + (A + B + 1) := by rw [h]
        _ = -C := by rw [hABC']; ring
    · simp [routeEOpenPortSectionPairMap, routeEOpenPortChart,
        routeEOpenPortHMap, h]
  · apply Prod.ext
    · simp [routeEOpenPortSectionPairMap, routeEOpenPortChart,
        routeEOpenPortHMap, h]
      calc
        a + A + 1 + (b + B) = (a + b) + (A + B + 1) := by ring
        _ = (a + b) - C := by rw [hABC']; ring
    · simp [routeEOpenPortSectionPairMap, routeEOpenPortChart,
        routeEOpenPortHMap, h]

structure RouteEOpenPortAffineChartCertificate (m : Nat) [NeZero m] where
  A : ZMod m
  B : ZMod m
  C : ZMod m
  count_sum : A + B + C + 1 = 0
  C_unit : IsUnit C
  chartRank : ZMod m × ZMod m → ZMod (m ^ 2)
  chartRank_bijective : Function.Bijective chartRank
  chartRank_step :
    ∀ p, chartRank (routeEOpenPortHMap A C p) = chartRank p + 1

namespace RouteEOpenPortAffineChartCertificate

theorem H_single_cycle {m : Nat} [NeZero m]
    (cert : RouteEOpenPortAffineChartCertificate m) :
    IsSingleCycleMap (routeEOpenPortHMap cert.A cert.C) := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  haveI : NeZero (m ^ 2) := ⟨ne_of_gt (pow_pos hmpos 2)⟩
  exact Shared.single_cycle_of_zmod_rank
    (routeEOpenPortHMap cert.A cert.C)
    cert.chartRank cert.chartRank_bijective cert.chartRank_step

theorem sectionPairMap_conjugates_to_H {m : Nat} [NeZero m]
    (cert : RouteEOpenPortAffineChartCertificate m)
    (p : ZMod m × ZMod m) :
    routeEOpenPortChart (routeEOpenPortSectionPairMap cert.A cert.B p) =
      routeEOpenPortHMap cert.A cert.C (routeEOpenPortChart p) :=
  routeEOpenPortChart_sectionPairMap cert.A cert.B cert.C cert.count_sum p

theorem sectionPairMap_single_cycle {m : Nat} [NeZero m]
    (cert : RouteEOpenPortAffineChartCertificate m) :
    IsSingleCycleMap (routeEOpenPortSectionPairMap cert.A cert.B) := by
  refine Shared.single_cycle_of_equiv_conj
    (e := (routeEOpenPortChartEquiv (m := m)).symm)
    (f := routeEOpenPortSectionPairMap cert.A cert.B)
    (g := routeEOpenPortHMap cert.A cert.C)
    (H_single_cycle cert) ?_
  intro p
  calc
    routeEOpenPortChart
        (routeEOpenPortSectionPairMap cert.A cert.B
          ((routeEOpenPortChartEquiv (m := m)).symm p)) =
        routeEOpenPortHMap cert.A cert.C
          (routeEOpenPortChart ((routeEOpenPortChartEquiv (m := m)).symm p)) :=
      sectionPairMap_conjugates_to_H cert ((routeEOpenPortChartEquiv (m := m)).symm p)
    _ = routeEOpenPortHMap cert.A cert.C p := by
      simpa [routeEOpenPortChartEquiv] using
        congrArg (routeEOpenPortHMap cert.A cert.C)
          ((routeEOpenPortChartEquiv (m := m)).right_inv p)

end RouteEOpenPortAffineChartCertificate

structure RouteEOpenPortFiniteOdometerCertificate (m : Nat) [NeZero m] where
  A : ZMod m
  B : ZMod m
  C : ZMod m
  count_sum : A + B + C + 1 = 0
  chartIdx : ZMod m × ZMod m ≃ Fin m × Fin m
  chartIdx_step :
    ∀ p, chartIdx (routeEOpenPortHMap A C p) =
      routeEOpenPortFinSquareSucc (chartIdx p)

namespace RouteEOpenPortFiniteOdometerCertificate

theorem H_single_cycle {m : Nat} [NeZero m]
    (cert : RouteEOpenPortFiniteOdometerCertificate m) :
    IsSingleCycleMap (routeEOpenPortHMap cert.A cert.C) := by
  refine Shared.single_cycle_of_equiv_conj
    (e := cert.chartIdx.symm)
    (f := routeEOpenPortHMap cert.A cert.C)
    (g := routeEOpenPortFinSquareSucc (m := m))
    (routeEOpenPortFinSquareSucc_single_cycle m) ?_
  intro I
  calc
    cert.chartIdx
        (routeEOpenPortHMap cert.A cert.C (cert.chartIdx.symm I)) =
        routeEOpenPortFinSquareSucc (cert.chartIdx (cert.chartIdx.symm I)) :=
      cert.chartIdx_step (cert.chartIdx.symm I)
    _ = routeEOpenPortFinSquareSucc I := by simp

theorem sectionPairMap_conjugates_to_H {m : Nat} [NeZero m]
    (cert : RouteEOpenPortFiniteOdometerCertificate m)
    (p : ZMod m × ZMod m) :
    routeEOpenPortChart (routeEOpenPortSectionPairMap cert.A cert.B p) =
      routeEOpenPortHMap cert.A cert.C (routeEOpenPortChart p) :=
  routeEOpenPortChart_sectionPairMap cert.A cert.B cert.C cert.count_sum p

theorem sectionPairMap_single_cycle {m : Nat} [NeZero m]
    (cert : RouteEOpenPortFiniteOdometerCertificate m) :
    IsSingleCycleMap (routeEOpenPortSectionPairMap cert.A cert.B) := by
  refine Shared.single_cycle_of_equiv_conj
    (e := (routeEOpenPortChartEquiv (m := m)).symm)
    (f := routeEOpenPortSectionPairMap cert.A cert.B)
    (g := routeEOpenPortHMap cert.A cert.C)
    (H_single_cycle cert) ?_
  intro p
  calc
    routeEOpenPortChart
        (routeEOpenPortSectionPairMap cert.A cert.B
          ((routeEOpenPortChartEquiv (m := m)).symm p)) =
        routeEOpenPortHMap cert.A cert.C
          (routeEOpenPortChart ((routeEOpenPortChartEquiv (m := m)).symm p)) :=
      sectionPairMap_conjugates_to_H cert ((routeEOpenPortChartEquiv (m := m)).symm p)
    _ = routeEOpenPortHMap cert.A cert.C p := by
      simpa [routeEOpenPortChartEquiv] using
        congrArg (routeEOpenPortHMap cert.A cert.C)
          ((routeEOpenPortChartEquiv (m := m)).right_inv p)

end RouteEOpenPortFiniteOdometerCertificate

noncomputable def routeEOpenPortCanonicalChartIdx {m : Nat} [NeZero m] :
    ZMod m × ZMod m ≃ Fin m × Fin m where
  toFun p :=
    ((finZModEquiv m).symm (-p.2 - p.1),
      (finZModEquiv m).symm (-1 - p.1))
  invFun I :=
    let sigma : ZMod m := -1 - (finZModEquiv m I.2)
    (sigma, -(finZModEquiv m I.1) - sigma)
  left_inv := by
    intro p
    rcases p with ⟨sigma, a⟩
    simp [finZModEquiv]
  right_inv := by
    intro I
    rcases I with ⟨i, j⟩
    apply Prod.ext
    · apply Fin.ext
      simp only [neg_sub, sub_neg_eq_add, add_sub_cancel_left, Equiv.symm_apply_apply]
    · apply Fin.ext
      simp only [sub_sub_cancel, Equiv.symm_apply_apply]

theorem routeEOpenPortCanonicalColumn_last {m : Nat} [NeZero m] :
    ((finZModEquiv m).symm (-1 : ZMod m)).val + 1 = m := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hcast :
      ((((finZModEquiv m).symm (-1 : ZMod m)).val : Nat) : ZMod m) = -1 := by
    simp [finZModEquiv]
  have htarget : (((m - 1 : Nat) : ZMod m)) = -1 := by
    have hsum : (((m - 1) + 1 : Nat) : ZMod m) = (0 : ZMod m) := by
      rw [show (m - 1) + 1 = m by omega]
      simp
    rw [Nat.cast_add, Nat.cast_one] at hsum
    rw [add_comm] at hsum
    exact eq_neg_of_add_eq_zero_right hsum
  have hv : ((finZModEquiv m).symm (-1 : ZMod m)).val = m - 1 := by
    apply zmod_nat_eq_of_lt (m := m)
    · exact ((finZModEquiv m).symm (-1 : ZMod m)).isLt
    · exact Nat.sub_lt hmpos Nat.one_pos
    · simpa [htarget] using hcast
  omega

theorem routeEOpenPortCanonicalColumn_lt_of_ne_zero {m : Nat} [NeZero m]
    {sigma : ZMod m} (hsigma : sigma ≠ 0) :
    ((finZModEquiv m).symm (-1 - sigma)).val + 1 < m := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  by_contra hlt
  have hjle : ((finZModEquiv m).symm (-1 - sigma)).val + 1 ≤ m :=
    Nat.succ_le_of_lt ((finZModEquiv m).symm (-1 - sigma)).isLt
  have hj : ((finZModEquiv m).symm (-1 - sigma)).val + 1 = m := by omega
  have hcast :
      ((((finZModEquiv m).symm (-1 - sigma)).val : Nat) : ZMod m) =
        -1 - sigma := by
    simp [finZModEquiv]
  have htarget :
      ((((finZModEquiv m).symm (-1 - sigma)).val : Nat) : ZMod m) = -1 := by
    have hv : ((finZModEquiv m).symm (-1 - sigma)).val = m - 1 := by omega
    rw [hv]
    have hsum : (((m - 1) + 1 : Nat) : ZMod m) = (0 : ZMod m) := by
      rw [show (m - 1) + 1 = m by omega]
      simp
    rw [Nat.cast_add, Nat.cast_one] at hsum
    rw [add_comm] at hsum
    exact eq_neg_of_add_eq_zero_right hsum
  have hsigma0 : sigma = 0 := by
    have h : (-1 : ZMod m) = -1 - sigma := htarget.symm.trans hcast
    have h2 := congrArg (fun x : ZMod m => x + 1) h
    have hneg : -sigma = 0 := by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h2.symm
    exact neg_eq_zero.mp hneg
  exact hsigma hsigma0

structure RouteEOpenPortCanonicalChartStepTarget (m : Nat) [NeZero m] : Prop where
  chartIdx_step :
    ∀ p, routeEOpenPortCanonicalChartIdx
        (routeEOpenPortHMap (0 : ZMod m) (1 : ZMod m) p) =
      routeEOpenPortFinSquareSucc (routeEOpenPortCanonicalChartIdx p)

namespace RouteEOpenPortCanonicalChartStepTarget

set_option linter.flexible false in
theorem unconditional {m : Nat} [NeZero m] :
    RouteEOpenPortCanonicalChartStepTarget m := by
  refine ⟨?_⟩
  intro p
  rcases p with ⟨sigma, a⟩
  by_cases hsigma : sigma = 0
  · subst sigma
    have hcol :
        (routeEOpenPortCanonicalChartIdx ((0 : ZMod m), a)).2.val + 1 = m := by
      simpa [routeEOpenPortCanonicalChartIdx] using
        routeEOpenPortCanonicalColumn_last (m := m)
    rw [routeEOpenPortFinSquareSucc_of_last_col _ hcol]
    apply Prod.ext
    · simp [routeEOpenPortCanonicalChartIdx, routeEOpenPortHMap]
      simpa [finRotate_apply] using finZModEquiv_symm_add_one (-a)
    · simp [routeEOpenPortCanonicalChartIdx, routeEOpenPortHMap, finZModEquiv]
  · have hcol :
        (routeEOpenPortCanonicalChartIdx (sigma, a)).2.val + 1 < m := by
      simpa [routeEOpenPortCanonicalChartIdx] using
        routeEOpenPortCanonicalColumn_lt_of_ne_zero (m := m) hsigma
    rw [routeEOpenPortFinSquareSucc_of_col_lt _ hcol]
    apply Prod.ext
    · apply (Equiv.injective (finZModEquiv m))
      simp [routeEOpenPortCanonicalChartIdx, routeEOpenPortHMap, hsigma, finZModEquiv]
      ring
    · simp [routeEOpenPortCanonicalChartIdx, routeEOpenPortHMap, hsigma]
      rw [← finRotate_of_lt ((finZModEquiv m).symm (-1 - sigma)) hcol]
      rw [← finZModEquiv_symm_add_one (-1 - sigma)]
      apply (Equiv.injective (finZModEquiv m))
      simp [finZModEquiv]
      ring

noncomputable def finiteOdometerCertificate {m : Nat} [NeZero m]
    (target : RouteEOpenPortCanonicalChartStepTarget m) :
    RouteEOpenPortFiniteOdometerCertificate m where
  A := 0
  B := -2
  C := 1
  count_sum := by ring
  chartIdx := routeEOpenPortCanonicalChartIdx
  chartIdx_step := target.chartIdx_step

theorem H_single_cycle {m : Nat} [NeZero m]
    (target : RouteEOpenPortCanonicalChartStepTarget m) :
    IsSingleCycleMap (routeEOpenPortHMap (0 : ZMod m) (1 : ZMod m)) :=
  RouteEOpenPortFiniteOdometerCertificate.H_single_cycle
    (finiteOdometerCertificate target)

theorem sectionPairMap_single_cycle {m : Nat} [NeZero m]
    (target : RouteEOpenPortCanonicalChartStepTarget m) :
    IsSingleCycleMap (routeEOpenPortSectionPairMap (0 : ZMod m) (-2 : ZMod m)) :=
  RouteEOpenPortFiniteOdometerCertificate.sectionPairMap_single_cycle
    (finiteOdometerCertificate target)

end RouteEOpenPortCanonicalChartStepTarget

theorem routeEOpenPortCanonicalH_single_cycle {m : Nat} [NeZero m] :
    IsSingleCycleMap (routeEOpenPortHMap (0 : ZMod m) (1 : ZMod m)) :=
  RouteEOpenPortCanonicalChartStepTarget.H_single_cycle
    RouteEOpenPortCanonicalChartStepTarget.unconditional

theorem routeEOpenPortCanonicalSectionPairMap_single_cycle {m : Nat} [NeZero m] :
    IsSingleCycleMap (routeEOpenPortSectionPairMap (0 : ZMod m) (-2 : ZMod m)) :=
  RouteEOpenPortCanonicalChartStepTarget.sectionPairMap_single_cycle
    RouteEOpenPortCanonicalChartStepTarget.unconditional

def routeEThetaPoint {m : Nat} (slot : Color) (a : ZMod m) : Vec4 m :=
  if slot = 0 then ![a, 0, 0, -a] else
  if slot = 1 then ![0, a, 0, 0] else
  if slot = 2 then ![-a, 0, a, 0] else
  if slot = 3 then ![0, -a, 0, a] else
  ![0, 0, -a, 0]

def routeEThetaVec {m : Nat} (slot : Color) (a : ZMod m) : Vec5 m :=
  if slot = 0 then ![0, a, 0, 0, -a] else
  if slot = 1 then ![-a, 0, a, 0, 0] else
  if slot = 2 then ![0, -a, 0, a, 0] else
  if slot = 3 then ![0, 0, -a, 0, a] else
  ![a, 0, 0, -a, 0]

theorem root5_routeEThetaVec {m : Nat} (slot : Color) (a : ZMod m) :
    Root5 m (routeEThetaVec slot a) := by
  fin_cases slot <;>
    simp [routeEThetaVec, Root5, sum5, Fin.sum_univ_five]

theorem rootZ_routeEThetaVec {m : Nat} (slot : Color) (a : ZMod m) :
    rootZ (routeEThetaVec slot a) = routeEThetaPoint slot a := by
  fin_cases slot <;>
    funext i <;>
    fin_cases i <;>
    simp [rootZ, routeEThetaVec, routeEThetaPoint, fin4ToFin5]

theorem rootOfZ_routeEThetaPoint {m : Nat} (slot : Color) (a : ZMod m) :
    (rootOfZ (routeEThetaPoint slot a)).1 = routeEThetaVec slot a := by
  fin_cases slot <;>
    ext i <;>
    fin_cases i <;>
    simp [rootOfZ, routeEThetaPoint, routeEThetaVec]

theorem routeEThetaVec_port_zero {m : Nat} (slot : Color) (a : ZMod m) :
    routeEThetaVec slot a (fin5AddNat slot 2) = 0 := by
  fin_cases slot <;> simp [routeEThetaVec, fin5AddNat]

theorem routeEThetaVec_pos_param {m : Nat} (slot : Color) (a : ZMod m) :
    routeEThetaVec slot a (fin5AddNat slot 1) = a := by
  fin_cases slot <;> simp [routeEThetaVec, fin5AddNat]

theorem routeEThetaVec_neg_param {m : Nat} (slot : Color) (a : ZMod m) :
    routeEThetaVec slot a (fin5AddNat slot 4) = -a := by
  fin_cases slot <;> simp [routeEThetaVec, fin5AddNat]

theorem LambdaE_routeEThetaVec {m : Nat} (slot : Color) {a : ZMod m}
    (ha : a ≠ 0) :
    LambdaE (zeroMaskMinusOne (routeEThetaVec slot a)) slot =
      fin5AddNat slot 2 := by
  have hneg : -a ≠ 0 := by
    intro h
    exact ha (neg_eq_zero.mp h)
  fin_cases slot <;>
    rw [zeroMaskMinusOne_eq_mask5] <;>
    simp [LambdaE, routeEThetaVec, mask5, row5, fin5AddNat, ha, hneg]

theorem LambdaE_routeEThetaSeam {m : Nat} (slot : Color)
    (a : RouteENonzeroSeam m) :
    LambdaE (zeroMaskMinusOne (routeEThetaVec slot a.1)) slot =
      fin5AddNat slot 2 :=
  LambdaE_routeEThetaVec slot a.2

theorem routeEThetaPoint_injective {m : Nat} (slot : Color) :
    Function.Injective (routeEThetaPoint (m := m) slot) := by
  intro a b h
  fin_cases slot
  · have h0 := congrArg (fun z : Vec4 m => z 0) h
    simpa [routeEThetaPoint] using h0
  · have h1 := congrArg (fun z : Vec4 m => z 1) h
    simpa [routeEThetaPoint] using h1
  · have h2 := congrArg (fun z : Vec4 m => z 2) h
    simpa [routeEThetaPoint] using h2
  · have h3 := congrArg (fun z : Vec4 m => z 3) h
    simpa [routeEThetaPoint] using h3
  · have h2 := congrArg (fun z : Vec4 m => z 2) h
    exact neg_injective (by simpa [routeEThetaPoint] using h2)

def routeEThetaSeamPoint {m : Nat} (slot : Color) :
    RouteENonzeroSeam m → Vec4 m :=
  fun a => routeEThetaPoint (m := m) slot a.1

theorem routeEThetaSeamPoint_injective {m : Nat} (slot : Color) :
    Function.Injective (routeEThetaSeamPoint (m := m) slot) := by
  intro a b h
  apply Subtype.ext
  exact routeEThetaPoint_injective slot h

structure RouteESmallSeamCertificate (m : Nat) [NeZero m] where
  data : D5EvenSeamData m
  routeCounts : RouteECounts m
  seam : Type
  seamFintype : Fintype seam
  seamPoint : seam → Vec4 m
  seamPoint_injective : Function.Injective seamPoint
  seamReturn : Color → seam → seam
  returnTime : Color → seam → Nat
  returnTime_pos : ∀ c a, 0 < returnTime c a
  firstReturn_equation :
    ∀ c a,
      (seamRootReturn data c)^[returnTime c a] (seamPoint a) =
        seamPoint (seamReturn c a)
  firstReturn_minimal :
    ∀ c a k, 0 < k → k < returnTime c a →
      ¬ ∃ b, (seamRootReturn data c)^[k] (seamPoint a) = seamPoint b
  seamReturn_single :
    ∀ c, letI := seamFintype; IsSingleCycleMap (seamReturn c)
  returnTime_sum :
    ∀ c, letI := seamFintype;
      Finset.univ.sum (fun a : seam => returnTime c a) = m ^ 4

namespace RouteESmallSeamCertificate

theorem seamRootReturn_single_cycle {m : Nat} [NeZero m]
    (cert : RouteESmallSeamCertificate m) (c : Color) :
    IsSingleCycleMap (seamRootReturn cert.data c) := by
  letI := cert.seamFintype
  exact single_cycle_of_first_return_sum
    (f := seamRootReturn cert.data c)
    (base := cert.seamPoint)
    (next := cert.seamReturn c)
    (time := cert.returnTime c)
    (hf := seamRootReturn_bijective cert.data c)
    (hbase_inj := cert.seamPoint_injective)
    (hreturn := cert.firstReturn_equation c)
    (hfirst := cert.firstReturn_minimal c)
    (hnext := cert.seamReturn_single c)
    (hsum := by
      rw [cert.returnTime_sum c]
      exact (card_vec4 m).symm)

theorem orbitTarget {m : Nat} [NeZero m]
    (cert : RouteESmallSeamCertificate m) :
    D5EvenSeamReturnOrbitTarget cert.data := by
  intro c x y
  exact (cert.seamRootReturn_single_cycle c).2 x y

def toSeamReturnCertificateTarget {m : Nat} [NeZero m]
    (cert : RouteESmallSeamCertificate m) :
    D5EvenSeamReturnCertificateTarget m :=
  ⟨cert.data, D5EvenSeamReturnCompatible.of_seam_data cert.data,
    cert.orbitTarget⟩

theorem toHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteESmallSeamCertificate m) :
    HamiltonDecompositionD5 m :=
  D5_even_from_return_certificate cert.toSeamReturnCertificateTarget

theorem toTorusHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteESmallSeamCertificate m) :
    TorusHamiltonDecompositionD5 m :=
  D5_even_torus_from_return_certificate cert.toSeamReturnCertificateTarget

theorem toCayleyHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteESmallSeamCertificate m) :
    CayleyHamiltonDecompositionD5 m :=
  D5_even_cayley_from_return_certificate cert.toSeamReturnCertificateTarget

end RouteESmallSeamCertificate

structure RouteENonopenSmallSeamCertificate (m : Nat) [NeZero m] where
  data : D5EvenSeamData m
  routeCounts : RouteECounts m
  slot : Color
  seamPoint : RouteENonzeroSeam m → Vec4 m
  seamPoint_injective : Function.Injective seamPoint
  seamReturn : Color → RouteENonzeroSeam m → RouteENonzeroSeam m
  returnTime : Color → RouteENonzeroSeam m → Nat
  returnTime_pos : ∀ c a, 0 < returnTime c a
  firstReturn_equation :
    ∀ c a,
      (seamRootReturn data c)^[returnTime c a] (seamPoint a) =
        seamPoint (seamReturn c a)
  firstReturn_minimal :
    ∀ c a k, 0 < k → k < returnTime c a →
      ¬ ∃ b, (seamRootReturn data c)^[k] (seamPoint a) = seamPoint b
  seamReturn_single :
    ∀ c, IsSingleCycleMap (seamReturn c)
  returnTime_sum :
    ∀ c, Finset.univ.sum (fun a : RouteENonzeroSeam m => returnTime c a) = m ^ 4

namespace RouteENonopenSmallSeamCertificate

theorem seam_card {m : Nat} [NeZero m]
    (_cert : RouteENonopenSmallSeamCertificate m) :
    Fintype.card (RouteENonzeroSeam m) = m - 1 :=
  card_routeENonzeroSeam m

theorem returnTime_sum_card_form {m : Nat} [NeZero m]
    (cert : RouteENonopenSmallSeamCertificate m) (c : Color) :
    Finset.univ.sum (fun a : RouteENonzeroSeam m => cert.returnTime c a) =
      Fintype.card (Vec4 m) := by
  rw [cert.returnTime_sum c]
  exact (card_vec4 m).symm

def toSmallSeamCertificate {m : Nat} [NeZero m]
    (cert : RouteENonopenSmallSeamCertificate m) :
    RouteESmallSeamCertificate m where
  data := cert.data
  routeCounts := cert.routeCounts
  seam := RouteENonzeroSeam m
  seamFintype := inferInstance
  seamPoint := cert.seamPoint
  seamPoint_injective := cert.seamPoint_injective
  seamReturn := cert.seamReturn
  returnTime := cert.returnTime
  returnTime_pos := cert.returnTime_pos
  firstReturn_equation := cert.firstReturn_equation
  firstReturn_minimal := cert.firstReturn_minimal
  seamReturn_single := by
    intro c
    simpa using cert.seamReturn_single c
  returnTime_sum := cert.returnTime_sum

theorem seamRootReturn_single_cycle {m : Nat} [NeZero m]
    (cert : RouteENonopenSmallSeamCertificate m) (c : Color) :
    IsSingleCycleMap (seamRootReturn cert.data c) :=
  cert.toSmallSeamCertificate.seamRootReturn_single_cycle c

theorem orbitTarget {m : Nat} [NeZero m]
    (cert : RouteENonopenSmallSeamCertificate m) :
    D5EvenSeamReturnOrbitTarget cert.data :=
  cert.toSmallSeamCertificate.orbitTarget

theorem toHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteENonopenSmallSeamCertificate m) :
    HamiltonDecompositionD5 m :=
  cert.toSmallSeamCertificate.toHamiltonDecomposition

theorem toTorusHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteENonopenSmallSeamCertificate m) :
    TorusHamiltonDecompositionD5 m :=
  cert.toSmallSeamCertificate.toTorusHamiltonDecomposition

theorem toCayleyHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteENonopenSmallSeamCertificate m) :
    CayleyHamiltonDecompositionD5 m :=
  cert.toSmallSeamCertificate.toCayleyHamiltonDecomposition

end RouteENonopenSmallSeamCertificate

structure RouteEThetaSmallSeamCertificate (m : Nat) [NeZero m] where
  data : D5EvenSeamData m
  routeCounts : RouteECounts m
  slot : Color
  routeCounts_slot : routeCounts.slot = slot
  seamReturn : Color → RouteENonzeroSeam m → RouteENonzeroSeam m
  returnTime : Color → RouteENonzeroSeam m → Nat
  returnTime_pos : ∀ c a, 0 < returnTime c a
  firstReturn_equation :
    ∀ c a,
      (seamRootReturn data c)^[returnTime c a] (routeEThetaSeamPoint slot a) =
        routeEThetaSeamPoint slot (seamReturn c a)
  firstReturn_minimal :
    ∀ c a k, 0 < k → k < returnTime c a →
      ¬ ∃ b, (seamRootReturn data c)^[k] (routeEThetaSeamPoint slot a) =
        routeEThetaSeamPoint slot b
  seamReturn_single :
    ∀ c, IsSingleCycleMap (seamReturn c)
  returnTime_sum :
    ∀ c, Finset.univ.sum (fun a : RouteENonzeroSeam m => returnTime c a) = m ^ 4

namespace RouteEThetaSmallSeamCertificate

theorem seam_card {m : Nat} [NeZero m]
    (_cert : RouteEThetaSmallSeamCertificate m) :
    Fintype.card (RouteENonzeroSeam m) = m - 1 :=
  card_routeENonzeroSeam m

theorem returnTime_sum_card_form {m : Nat} [NeZero m]
    (cert : RouteEThetaSmallSeamCertificate m) (c : Color) :
    Finset.univ.sum (fun a : RouteENonzeroSeam m => cert.returnTime c a) =
      Fintype.card (Vec4 m) := by
  rw [cert.returnTime_sum c]
  exact (card_vec4 m).symm

def toNonopenSmallSeamCertificate {m : Nat} [NeZero m]
    (cert : RouteEThetaSmallSeamCertificate m) :
    RouteENonopenSmallSeamCertificate m where
  data := cert.data
  routeCounts := cert.routeCounts
  slot := cert.slot
  seamPoint := routeEThetaSeamPoint cert.slot
  seamPoint_injective := routeEThetaSeamPoint_injective cert.slot
  seamReturn := cert.seamReturn
  returnTime := cert.returnTime
  returnTime_pos := cert.returnTime_pos
  firstReturn_equation := cert.firstReturn_equation
  firstReturn_minimal := cert.firstReturn_minimal
  seamReturn_single := cert.seamReturn_single
  returnTime_sum := cert.returnTime_sum

theorem seamRootReturn_single_cycle {m : Nat} [NeZero m]
    (cert : RouteEThetaSmallSeamCertificate m) (c : Color) :
    IsSingleCycleMap (seamRootReturn cert.data c) :=
  cert.toNonopenSmallSeamCertificate.seamRootReturn_single_cycle c

theorem orbitTarget {m : Nat} [NeZero m]
    (cert : RouteEThetaSmallSeamCertificate m) :
    D5EvenSeamReturnOrbitTarget cert.data :=
  cert.toNonopenSmallSeamCertificate.orbitTarget

theorem toHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteEThetaSmallSeamCertificate m) :
    HamiltonDecompositionD5 m :=
  cert.toNonopenSmallSeamCertificate.toHamiltonDecomposition

theorem toTorusHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteEThetaSmallSeamCertificate m) :
    TorusHamiltonDecompositionD5 m :=
  cert.toNonopenSmallSeamCertificate.toTorusHamiltonDecomposition

theorem toCayleyHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteEThetaSmallSeamCertificate m) :
    CayleyHamiltonDecompositionD5 m :=
  cert.toNonopenSmallSeamCertificate.toCayleyHamiltonDecomposition

end RouteEThetaSmallSeamCertificate

structure RouteEThetaRankedSmallSeamCertificate (m : Nat) [NeZero m]
    [NeZero (m - 1)] where
  data : D5EvenSeamData m
  routeCounts : RouteECounts m
  slot : Color
  routeCounts_slot : routeCounts.slot = slot
  seamReturn : Color → RouteENonzeroSeam m → RouteENonzeroSeam m
  returnTime : Color → RouteENonzeroSeam m → Nat
  returnTime_pos : ∀ c a, 0 < returnTime c a
  firstReturn_equation :
    ∀ c a,
      (seamRootReturn data c)^[returnTime c a] (routeEThetaSeamPoint slot a) =
        routeEThetaSeamPoint slot (seamReturn c a)
  firstReturn_minimal :
    ∀ c a k, 0 < k → k < returnTime c a →
      ¬ ∃ b, (seamRootReturn data c)^[k] (routeEThetaSeamPoint slot a) =
        routeEThetaSeamPoint slot b
  seamRank : Color → RouteENonzeroSeam m → ZMod (m - 1)
  seamRank_bijective : ∀ c, Function.Bijective (seamRank c)
  seamRank_step :
    ∀ c a, seamRank c (seamReturn c a) = seamRank c a + 1
  returnTime_sum :
    ∀ c, Finset.univ.sum (fun a : RouteENonzeroSeam m => returnTime c a) = m ^ 4

namespace RouteEThetaRankedSmallSeamCertificate

theorem seamReturn_single {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedSmallSeamCertificate m) (c : Color) :
    IsSingleCycleMap (cert.seamReturn c) :=
  Shared.single_cycle_of_zmod_rank
    (f := cert.seamReturn c)
    (rank := cert.seamRank c)
    (cert.seamRank_bijective c)
    (cert.seamRank_step c)

def toThetaSmallSeamCertificate {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedSmallSeamCertificate m) :
    RouteEThetaSmallSeamCertificate m where
  data := cert.data
  routeCounts := cert.routeCounts
  slot := cert.slot
  routeCounts_slot := cert.routeCounts_slot
  seamReturn := cert.seamReturn
  returnTime := cert.returnTime
  returnTime_pos := cert.returnTime_pos
  firstReturn_equation := cert.firstReturn_equation
  firstReturn_minimal := cert.firstReturn_minimal
  seamReturn_single := cert.seamReturn_single
  returnTime_sum := cert.returnTime_sum

theorem seamRootReturn_single_cycle {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedSmallSeamCertificate m) (c : Color) :
    IsSingleCycleMap (seamRootReturn cert.data c) :=
  cert.toThetaSmallSeamCertificate.seamRootReturn_single_cycle c

theorem orbitTarget {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedSmallSeamCertificate m) :
    D5EvenSeamReturnOrbitTarget cert.data :=
  cert.toThetaSmallSeamCertificate.orbitTarget

theorem toHamiltonDecomposition {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedSmallSeamCertificate m) :
    HamiltonDecompositionD5 m :=
  cert.toThetaSmallSeamCertificate.toHamiltonDecomposition

theorem toTorusHamiltonDecomposition {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedSmallSeamCertificate m) :
    TorusHamiltonDecompositionD5 m :=
  cert.toThetaSmallSeamCertificate.toTorusHamiltonDecomposition

theorem toCayleyHamiltonDecomposition {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedSmallSeamCertificate m) :
    CayleyHamiltonDecompositionD5 m :=
  cert.toThetaSmallSeamCertificate.toCayleyHamiltonDecomposition

end RouteEThetaRankedSmallSeamCertificate

structure RouteEThetaPiecewiseTranslationCertificate (m : Nat) [NeZero m] extends
    RouteEThetaSmallSeamCertificate m where
  blocks : Color → List (RouteESeamTranslationBlock m)
  block_cover :
    ∀ c a, ∃ block, block ∈ blocks c ∧ block.contains a
  block_disjoint :
    ∀ c a block₁ block₂,
      block₁ ∈ blocks c → block₂ ∈ blocks c →
      block₁.contains a → block₂.contains a → block₁ = block₂
  block_translation :
    ∀ c block,
      block ∈ blocks c →
        block.translationFormula (seamReturn c)

namespace RouteEThetaPiecewiseTranslationCertificate

theorem seamRootReturn_single_cycle {m : Nat} [NeZero m]
    (cert : RouteEThetaPiecewiseTranslationCertificate m) (c : Color) :
    IsSingleCycleMap (seamRootReturn cert.data c) :=
  cert.toRouteEThetaSmallSeamCertificate.seamRootReturn_single_cycle c

theorem orbitTarget {m : Nat} [NeZero m]
    (cert : RouteEThetaPiecewiseTranslationCertificate m) :
    D5EvenSeamReturnOrbitTarget cert.data :=
  cert.toRouteEThetaSmallSeamCertificate.orbitTarget

theorem toHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteEThetaPiecewiseTranslationCertificate m) :
    HamiltonDecompositionD5 m :=
  cert.toRouteEThetaSmallSeamCertificate.toHamiltonDecomposition

theorem toTorusHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteEThetaPiecewiseTranslationCertificate m) :
    TorusHamiltonDecompositionD5 m :=
  cert.toRouteEThetaSmallSeamCertificate.toTorusHamiltonDecomposition

theorem toCayleyHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteEThetaPiecewiseTranslationCertificate m) :
    CayleyHamiltonDecompositionD5 m :=
  cert.toRouteEThetaSmallSeamCertificate.toCayleyHamiltonDecomposition

end RouteEThetaPiecewiseTranslationCertificate

structure RouteEThetaRankedPiecewiseTranslationCertificate (m : Nat) [NeZero m]
    [NeZero (m - 1)] extends RouteEThetaRankedSmallSeamCertificate m where
  blocks : Color → List (RouteESeamTranslationBlock m)
  block_cover :
    ∀ c a, ∃ block, block ∈ blocks c ∧ block.contains a
  block_disjoint :
    ∀ c a block₁ block₂,
      block₁ ∈ blocks c → block₂ ∈ blocks c →
      block₁.contains a → block₂.contains a → block₁ = block₂
  block_translation :
    ∀ c block,
      block ∈ blocks c →
        block.translationFormula (seamReturn c)

namespace RouteEThetaRankedPiecewiseTranslationCertificate

def toThetaPiecewiseTranslationCertificate {m : Nat} [NeZero m]
    [NeZero (m - 1)] (cert : RouteEThetaRankedPiecewiseTranslationCertificate m) :
    RouteEThetaPiecewiseTranslationCertificate m where
  toRouteEThetaSmallSeamCertificate :=
    cert.toRouteEThetaRankedSmallSeamCertificate.toThetaSmallSeamCertificate
  blocks := cert.blocks
  block_cover := cert.block_cover
  block_disjoint := cert.block_disjoint
  block_translation := cert.block_translation

theorem seamRootReturn_single_cycle {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedPiecewiseTranslationCertificate m) (c : Color) :
    IsSingleCycleMap (seamRootReturn cert.data c) :=
  cert.toThetaPiecewiseTranslationCertificate.seamRootReturn_single_cycle c

theorem orbitTarget {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedPiecewiseTranslationCertificate m) :
    D5EvenSeamReturnOrbitTarget cert.data :=
  cert.toThetaPiecewiseTranslationCertificate.orbitTarget

theorem toHamiltonDecomposition {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedPiecewiseTranslationCertificate m) :
    HamiltonDecompositionD5 m :=
  cert.toThetaPiecewiseTranslationCertificate.toHamiltonDecomposition

theorem toTorusHamiltonDecomposition {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedPiecewiseTranslationCertificate m) :
    TorusHamiltonDecompositionD5 m :=
  cert.toThetaPiecewiseTranslationCertificate.toTorusHamiltonDecomposition

theorem toCayleyHamiltonDecomposition {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedPiecewiseTranslationCertificate m) :
    CayleyHamiltonDecompositionD5 m :=
  cert.toThetaPiecewiseTranslationCertificate.toCayleyHamiltonDecomposition

end RouteEThetaRankedPiecewiseTranslationCertificate

namespace RouteEB20

/-!
Trace-facing B20 target.

The expected B20 seam map, block cover, and cycle proof are already closed
above.  The remaining branch-specific work is to prove that the concrete
Route-E trace first-returns to this map with the claimed positive return
times and no earlier seam hits.  Once those trace facts and the return-time
sum are supplied, the theorem below packages them as the existing
piecewise-translation certificate.
-/

structure ThetaTraceTarget (q : Nat) where
  data : D5EvenSeamData (modulus q)
  returnTime : Color → RouteENonzeroSeam (modulus q) → Nat
  returnTime_pos : ∀ c a, 0 < returnTime c a
  firstReturn_equation :
    ∀ c a,
      (seamRootReturn data c)^[returnTime c a] (routeEThetaSeamPoint 0 a) =
        routeEThetaSeamPoint 0 (seamMap q a)
  firstReturn_minimal :
    ∀ c a k, 0 < k → k < returnTime c a →
      ¬ ∃ b, (seamRootReturn data c)^[k] (routeEThetaSeamPoint 0 a) =
        routeEThetaSeamPoint 0 b
  returnTime_sum :
    ∀ c,
      Finset.univ.sum (fun a : RouteENonzeroSeam (modulus q) =>
        returnTime c a) = modulus q ^ 4

noncomputable def thetaPiecewiseCertificateOfTraceTarget (q : Nat)
    (target : ThetaTraceTarget q) :
    RouteEThetaPiecewiseTranslationCertificate (modulus q) where
  data := target.data
  routeCounts := routeCounts q
  slot := 0
  routeCounts_slot := rfl
  seamReturn := fun _ => seamMap q
  returnTime := target.returnTime
  returnTime_pos := target.returnTime_pos
  firstReturn_equation := target.firstReturn_equation
  firstReturn_minimal := target.firstReturn_minimal
  seamReturn_single := by
    intro _c
    exact seamMap_single_cycle q
  returnTime_sum := target.returnTime_sum
  blocks := fun _ => seamBlocks q
  block_cover := by
    intro _c a
    exact seamBlocks_cover q a
  block_disjoint := by
    intro _c a block₁ block₂ hmem₁ hmem₂ hcontains₁ hcontains₂
    exact seamBlocks_disjoint q a block₁ block₂ hmem₁ hmem₂ hcontains₁
      hcontains₂
  block_translation := by
    intro _c block hmem
    exact seamBlocks_translation q block hmem

theorem thetaPiecewiseTarget_of_traceTarget (q : Nat)
    (h : Nonempty (ThetaTraceTarget q)) :
    Nonempty (RouteEThetaPiecewiseTranslationCertificate (modulus q)) := by
  rcases h with ⟨target⟩
  exact ⟨thetaPiecewiseCertificateOfTraceTarget q target⟩

end RouteEB20

def D5EvenRouteEAllLargeEvenTarget : Prop :=
  ∀ (m : Nat) [NeZero m], Even m → 6 ≤ m →
    Nonempty (RouteESmallSeamCertificate m)

def D5EvenRouteENonopenAllLargeEvenTarget : Prop :=
  ∀ (m : Nat) [NeZero m], Even m → 6 ≤ m →
    Nonempty (RouteENonopenSmallSeamCertificate m)

def D5EvenRouteEThetaAllLargeEvenTarget : Prop :=
  ∀ (m : Nat) [NeZero m], Even m → 6 ≤ m →
    Nonempty (RouteEThetaSmallSeamCertificate m)

def D5EvenRouteEThetaRankedAllLargeEvenTarget : Prop :=
  ∀ (m : Nat) [NeZero m] [NeZero (m - 1)], Even m → 6 ≤ m →
    Nonempty (RouteEThetaRankedSmallSeamCertificate m)

def D5EvenRouteEThetaPiecewiseAllLargeEvenTarget : Prop :=
  ∀ (m : Nat) [NeZero m], Even m → 6 ≤ m →
    Nonempty (RouteEThetaPiecewiseTranslationCertificate m)

def D5EvenRouteEThetaRankedPiecewiseAllLargeEvenTarget : Prop :=
  ∀ (m : Nat) [NeZero m] [NeZero (m - 1)], Even m → 6 ≤ m →
    Nonempty (RouteEThetaRankedPiecewiseTranslationCertificate m)

def D5EvenRouteEM4FiniteTarget : Prop :=
  Nonempty (HamiltonDecompositionD5 4)

def D5EvenRouteEAllEvenHamiltonTarget : Prop :=
  ∀ (m : Nat) [NeZero m], Even m → 4 ≤ m →
    Nonempty (HamiltonDecompositionD5 m)

def D5EvenRouteEAllEvenTorusTarget : Prop :=
  ∀ (m : Nat) [NeZero m], Even m → 4 ≤ m →
    Nonempty (TorusHamiltonDecompositionD5 m)

def D5EvenRouteEAllEvenCayleyTarget : Prop :=
  ∀ (m : Nat) [NeZero m], Even m → 4 ≤ m →
    Nonempty (CayleyHamiltonDecompositionD5 m)

theorem D5EvenRouteEAllLargeEvenTarget.of_nonopen
    (h : D5EvenRouteENonopenAllLargeEvenTarget) :
    D5EvenRouteEAllLargeEvenTarget := by
  intro m _hm0 hmEven hm6
  rcases h m hmEven hm6 with ⟨cert⟩
  exact ⟨cert.toSmallSeamCertificate⟩

theorem D5EvenRouteENonopenAllLargeEvenTarget.of_theta
    (h : D5EvenRouteEThetaAllLargeEvenTarget) :
    D5EvenRouteENonopenAllLargeEvenTarget := by
  intro m _hm0 hmEven hm6
  rcases h m hmEven hm6 with ⟨cert⟩
  exact ⟨cert.toNonopenSmallSeamCertificate⟩

theorem D5EvenRouteEAllLargeEvenTarget.of_theta
    (h : D5EvenRouteEThetaAllLargeEvenTarget) :
    D5EvenRouteEAllLargeEvenTarget :=
  D5EvenRouteEAllLargeEvenTarget.of_nonopen
    (D5EvenRouteENonopenAllLargeEvenTarget.of_theta h)

theorem D5EvenRouteEThetaAllLargeEvenTarget.of_ranked
    (h : D5EvenRouteEThetaRankedAllLargeEvenTarget) :
    D5EvenRouteEThetaAllLargeEvenTarget := by
  intro m _hm0 hmEven hm6
  letI : NeZero (m - 1) := ⟨by omega⟩
  rcases h (m := m) hmEven hm6 with ⟨cert⟩
  exact ⟨cert.toThetaSmallSeamCertificate⟩

theorem D5EvenRouteENonopenAllLargeEvenTarget.of_ranked
    (h : D5EvenRouteEThetaRankedAllLargeEvenTarget) :
    D5EvenRouteENonopenAllLargeEvenTarget :=
  D5EvenRouteENonopenAllLargeEvenTarget.of_theta
    (D5EvenRouteEThetaAllLargeEvenTarget.of_ranked h)

theorem D5EvenRouteEAllLargeEvenTarget.of_ranked
    (h : D5EvenRouteEThetaRankedAllLargeEvenTarget) :
    D5EvenRouteEAllLargeEvenTarget :=
  D5EvenRouteEAllLargeEvenTarget.of_theta
    (D5EvenRouteEThetaAllLargeEvenTarget.of_ranked h)

theorem D5EvenRouteEThetaAllLargeEvenTarget.of_piecewise
    (h : D5EvenRouteEThetaPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEThetaAllLargeEvenTarget := by
  intro m _hm0 hmEven hm6
  rcases h m hmEven hm6 with ⟨cert⟩
  exact ⟨cert.toRouteEThetaSmallSeamCertificate⟩

theorem D5EvenRouteENonopenAllLargeEvenTarget.of_piecewise
    (h : D5EvenRouteEThetaPiecewiseAllLargeEvenTarget) :
    D5EvenRouteENonopenAllLargeEvenTarget :=
  D5EvenRouteENonopenAllLargeEvenTarget.of_theta
    (D5EvenRouteEThetaAllLargeEvenTarget.of_piecewise h)

theorem D5EvenRouteEAllLargeEvenTarget.of_piecewise
    (h : D5EvenRouteEThetaPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEAllLargeEvenTarget :=
  D5EvenRouteEAllLargeEvenTarget.of_theta
    (D5EvenRouteEThetaAllLargeEvenTarget.of_piecewise h)

theorem D5EvenRouteEThetaRankedAllLargeEvenTarget.of_ranked_piecewise
    (h : D5EvenRouteEThetaRankedPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEThetaRankedAllLargeEvenTarget := by
  intro m _hm0 _hm1 hmEven hm6
  rcases h (m := m) hmEven hm6 with ⟨cert⟩
  exact ⟨cert.toRouteEThetaRankedSmallSeamCertificate⟩

theorem D5EvenRouteEThetaPiecewiseAllLargeEvenTarget.of_ranked_piecewise
    (h : D5EvenRouteEThetaRankedPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEThetaPiecewiseAllLargeEvenTarget := by
  intro m _hm0 hmEven hm6
  letI : NeZero (m - 1) := ⟨by omega⟩
  rcases h (m := m) hmEven hm6 with ⟨cert⟩
  exact ⟨cert.toThetaPiecewiseTranslationCertificate⟩

theorem D5EvenRouteEThetaAllLargeEvenTarget.of_ranked_piecewise
    (h : D5EvenRouteEThetaRankedPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEThetaAllLargeEvenTarget :=
  D5EvenRouteEThetaAllLargeEvenTarget.of_ranked
    (D5EvenRouteEThetaRankedAllLargeEvenTarget.of_ranked_piecewise h)

theorem D5EvenRouteENonopenAllLargeEvenTarget.of_ranked_piecewise
    (h : D5EvenRouteEThetaRankedPiecewiseAllLargeEvenTarget) :
    D5EvenRouteENonopenAllLargeEvenTarget :=
  D5EvenRouteENonopenAllLargeEvenTarget.of_theta
    (D5EvenRouteEThetaAllLargeEvenTarget.of_ranked_piecewise h)

theorem D5EvenRouteEAllLargeEvenTarget.of_ranked_piecewise
    (h : D5EvenRouteEThetaRankedPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEAllLargeEvenTarget :=
  D5EvenRouteEAllLargeEvenTarget.of_theta
    (D5EvenRouteEThetaAllLargeEvenTarget.of_ranked_piecewise h)

theorem D5EvenRouteEAllEvenHamiltonTarget.of_large_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEAllLargeEvenTarget) :
    D5EvenRouteEAllEvenHamiltonTarget := by
  intro m _hm0 hmEven hm4le
  by_cases hm6 : 6 ≤ m
  · rcases hlarge m hmEven hm6 with ⟨cert⟩
    exact ⟨cert.toHamiltonDecomposition⟩
  · have hmle5 : m ≤ 5 := by omega
    interval_cases m
    · exact hm4
    · norm_num at hmEven

theorem D5EvenRouteEAllEvenHamiltonTarget.of_nonopen_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteENonopenAllLargeEvenTarget) :
    D5EvenRouteEAllEvenHamiltonTarget :=
  D5EvenRouteEAllEvenHamiltonTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_nonopen hlarge)

theorem D5EvenRouteEAllEvenHamiltonTarget.of_theta_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaAllLargeEvenTarget) :
    D5EvenRouteEAllEvenHamiltonTarget :=
  D5EvenRouteEAllEvenHamiltonTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_theta hlarge)

theorem D5EvenRouteEAllEvenHamiltonTarget.of_ranked_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaRankedAllLargeEvenTarget) :
    D5EvenRouteEAllEvenHamiltonTarget :=
  D5EvenRouteEAllEvenHamiltonTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_ranked hlarge)

theorem D5EvenRouteEAllEvenHamiltonTarget.of_piecewise_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEAllEvenHamiltonTarget :=
  D5EvenRouteEAllEvenHamiltonTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_piecewise hlarge)

theorem D5EvenRouteEAllEvenHamiltonTarget.of_ranked_piecewise_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaRankedPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEAllEvenHamiltonTarget :=
  D5EvenRouteEAllEvenHamiltonTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_ranked_piecewise hlarge)

theorem D5EvenRouteEAllEvenTorusTarget.of_large_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEAllLargeEvenTarget) :
    D5EvenRouteEAllEvenTorusTarget := by
  intro m _hm0 hmEven hm4le
  by_cases hm6 : 6 ≤ m
  · rcases hlarge m hmEven hm6 with ⟨cert⟩
    exact ⟨cert.toTorusHamiltonDecomposition⟩
  · have hmle5 : m ≤ 5 := by omega
    interval_cases m
    · rcases hm4 with ⟨h4⟩
      exact ⟨torusHamiltonDecomposition_of_model h4⟩
    · norm_num at hmEven

theorem D5EvenRouteEAllEvenTorusTarget.of_nonopen_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteENonopenAllLargeEvenTarget) :
    D5EvenRouteEAllEvenTorusTarget :=
  D5EvenRouteEAllEvenTorusTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_nonopen hlarge)

theorem D5EvenRouteEAllEvenTorusTarget.of_theta_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaAllLargeEvenTarget) :
    D5EvenRouteEAllEvenTorusTarget :=
  D5EvenRouteEAllEvenTorusTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_theta hlarge)

theorem D5EvenRouteEAllEvenTorusTarget.of_ranked_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaRankedAllLargeEvenTarget) :
    D5EvenRouteEAllEvenTorusTarget :=
  D5EvenRouteEAllEvenTorusTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_ranked hlarge)

theorem D5EvenRouteEAllEvenTorusTarget.of_piecewise_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEAllEvenTorusTarget :=
  D5EvenRouteEAllEvenTorusTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_piecewise hlarge)

theorem D5EvenRouteEAllEvenTorusTarget.of_ranked_piecewise_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaRankedPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEAllEvenTorusTarget :=
  D5EvenRouteEAllEvenTorusTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_ranked_piecewise hlarge)

theorem D5EvenRouteEAllEvenCayleyTarget.of_large_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEAllLargeEvenTarget) :
    D5EvenRouteEAllEvenCayleyTarget := by
  intro m _hm0 hmEven hm4le
  by_cases hm6 : 6 ≤ m
  · rcases hlarge m hmEven hm6 with ⟨cert⟩
    exact ⟨cert.toCayleyHamiltonDecomposition⟩
  · have hmle5 : m ≤ 5 := by omega
    interval_cases m
    · rcases hm4 with ⟨h4⟩
      exact ⟨cayleyHamiltonDecomposition_of_torus
        (torusHamiltonDecomposition_of_model h4)⟩
    · norm_num at hmEven

theorem D5EvenRouteEAllEvenCayleyTarget.of_nonopen_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteENonopenAllLargeEvenTarget) :
    D5EvenRouteEAllEvenCayleyTarget :=
  D5EvenRouteEAllEvenCayleyTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_nonopen hlarge)

theorem D5EvenRouteEAllEvenCayleyTarget.of_theta_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaAllLargeEvenTarget) :
    D5EvenRouteEAllEvenCayleyTarget :=
  D5EvenRouteEAllEvenCayleyTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_theta hlarge)

theorem D5EvenRouteEAllEvenCayleyTarget.of_ranked_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaRankedAllLargeEvenTarget) :
    D5EvenRouteEAllEvenCayleyTarget :=
  D5EvenRouteEAllEvenCayleyTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_ranked hlarge)

theorem D5EvenRouteEAllEvenCayleyTarget.of_piecewise_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEAllEvenCayleyTarget :=
  D5EvenRouteEAllEvenCayleyTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_piecewise hlarge)

theorem D5EvenRouteEAllEvenCayleyTarget.of_ranked_piecewise_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaRankedPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEAllEvenCayleyTarget :=
  D5EvenRouteEAllEvenCayleyTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_ranked_piecewise hlarge)

end D5Odd
