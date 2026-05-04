import RoundComposite.SeedSemigroup

namespace RoundComposite
namespace Concrete

def OddCoreHighGE13 (Solved : Nat → Nat → Prop) : Prop :=
  ∀ {d m : Nat}, 13 ≤ d → Odd d → 3 ≤ m → Odd m → d ≤ m →
    Solved d m

def OddCoreHighModulusPrefixCount (Solved : Nat → Nat → Prop) : Prop :=
  ∀ {d m : Nat}, Odd d → 5 ≤ d → 3 ≤ m → Odd m → d ≤ m →
    Solved d m

def OddCoreSmallGE13 (Solved : Nat → Nat → Prop) : Prop :=
  ∀ {d m : Nat}, 13 ≤ d → Odd d → 3 ≤ m → Odd m → m < d →
    Solved d m

def D11SmallModulusLiftFromD5Base (Solved : Nat → Nat → Prop) : Prop :=
  ∀ {m : Nat}, 3 ≤ m → Odd m → m < 11 →
    Solved 5 m →
    Solved 11 m

def OddCoreSmallModulusLiftOfBase (Solved : Nat → Nat → Prop) : Prop :=
  ∀ {d m b : Nat},
    Odd d → 13 ≤ d →
    Odd m → 3 ≤ m → m < d →
    Solved b m →
    2 * b < d ∧ d ≤ 3 * b →
    Solved d m

def OddCoreHighModulusPrefixCountGoal : Prop :=
  ∀ {d m : Nat}, Odd d → 5 ≤ d → Odd m → d ≤ m →
    StandardCayleySolved d m

def OddSuccessorHighModulusPrefixCountGoal : Prop :=
  ∀ {b m : Nat},
    5 ≤ b → Odd m → 2 * b + 1 ≤ m →
      StandardCayleySolved (2 * b + 1) m

def PrefixCountLayerRealizationGoal : Prop :=
  ∀ {d m : Nat} (hd2 : 2 ≤ d) (C : PrefixCount.Parts d),
    C.Admissible m →
    Nonempty (PrefixCount.LayerPermCounts d m (C.toMatrix hd2))

def PrefixCountGeometricCriterionGoal : Prop :=
  ∀ {d m : Nat} (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    PrefixCount.LayerPermCounts d m (C.toMatrix hd2) →
    StandardCayleySolved d m

abbrev PrefixCountRootState (d m : Nat) :=
  Fin (d - 1) → ZMod m

def prefixCountRootLayerEquivSucc (n m : Nat) :
    ZMod m × (Fin n → ZMod m) ≃ Shared.TorusVertex (n + 1) m where
  toFun tw := Fin.snoc tw.2 (tw.1 - ∑ j : Fin n, tw.2 j)
  invFun x := (∑ i : Fin (n + 1), x i, fun j : Fin n => x j.castSucc)
  left_inv := by
    intro tw
    ext
    · simp [Fin.sum_snoc]
    · simp
  right_inv := by
    intro x
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp
    · simp only [Fin.snoc_last]
      rw [Fin.sum_univ_castSucc]
      abel

def prefixCountRootStepSucc {n m : Nat}
    (i : Fin (n + 1)) (w : Fin n → ZMod m) : Fin n → ZMod m :=
  fun j => if i = j.castSucc then w j + 1 else w j

theorem prefixCountRootStepSucc_sum_castSucc {n m : Nat}
    (i : Fin n) (w : Fin n → ZMod m) :
    (∑ j : Fin n, prefixCountRootStepSucc i.castSucc w j)
      = (∑ j : Fin n, w j) + 1 := by
  classical
  calc
    (∑ j : Fin n, prefixCountRootStepSucc i.castSucc w j)
        = ∑ j : Fin n, (w j + if i = j then (1 : ZMod m) else 0) := by
            apply Finset.sum_congr rfl
            intro j _hj
            by_cases h : i = j
            · subst j
              simp [prefixCountRootStepSucc]
            · have hcast : i.castSucc ≠ j.castSucc := by
                intro hc
                exact h (Fin.castSucc_injective n hc)
              simp [prefixCountRootStepSucc, h, hcast]
    _ = (∑ j : Fin n, w j) + ∑ j : Fin n, (if i = j then (1 : ZMod m) else 0) := by
            rw [Finset.sum_add_distrib]
    _ = (∑ j : Fin n, w j) + 1 := by
            simp

theorem prefixCountRootStepSucc_sum_last {n m : Nat}
    (w : Fin n → ZMod m) :
    (∑ j : Fin n, prefixCountRootStepSucc (Fin.last n) w j)
      = ∑ j : Fin n, w j := by
  classical
  have hlast : ∀ j : Fin n, (Fin.last n : Fin (n + 1)) ≠ j.castSucc := by
    intro j h
    exact Fin.castSucc_ne_last j h.symm
  simp [prefixCountRootStepSucc, hlast]

theorem prefixCountRootLayerEquivSucc_step {n m : Nat}
    (i : Fin (n + 1)) (tw : ZMod m × (Fin n → ZMod m)) :
    prefixCountRootLayerEquivSucc n m
        (tw.1 + 1, prefixCountRootStepSucc i tw.2)
      =
      prefixCountRootLayerEquivSucc n m tw + Shared.torusBasis (n + 1) m i := by
  classical
  funext k
  rcases Fin.eq_castSucc_or_eq_last k with ⟨j, rfl⟩ | rfl
  · simp only [prefixCountRootLayerEquivSucc, Equiv.coe_fn_mk,
      Fin.snoc_castSucc, Pi.add_apply, Shared.torusBasis]
    by_cases h : i = j.castSucc
    · rw [prefixCountRootStepSucc, if_pos h, if_pos h.symm]
    · have h' : j.castSucc ≠ i := h ∘ Eq.symm
      rw [prefixCountRootStepSucc, if_neg h, if_neg h']
      simp
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp only [prefixCountRootLayerEquivSucc, Equiv.coe_fn_mk,
        Fin.snoc_last, Pi.add_apply, Shared.torusBasis]
      have hlast : (Fin.last n : Fin (n + 1)) ≠ j.castSucc :=
        (Fin.castSucc_ne_last j).symm
      simp [prefixCountRootStepSucc_sum_castSucc, hlast]
    · simp only [prefixCountRootLayerEquivSucc, Equiv.coe_fn_mk,
        Fin.snoc_last, Pi.add_apply, Shared.torusBasis]
      rw [prefixCountRootStepSucc_sum_last]
      simp
      ring_nf

def prefixCountRootLayerEquiv (d m : Nat) (hd1 : 1 ≤ d) :
    ZMod m × PrefixCountRootState d m ≃ Shared.TorusVertex d m :=
  (prefixCountRootLayerEquivSucc (d - 1) m).trans
    (Equiv.arrowCongr (finCongr (Nat.sub_add_cancel hd1)) (Equiv.refl _))

def prefixCountRootStep (d m : Nat) :
    Fin d → PrefixCountRootState d m → PrefixCountRootState d m :=
  fun i w j => if (i : Nat) = j then w j + 1 else w j

def prefixCountRootStepInv (d m : Nat) :
    Fin d → PrefixCountRootState d m → PrefixCountRootState d m :=
  fun i w j => if (i : Nat) = j then w j - 1 else w j

theorem prefixCountRootStep_eq_self_of_last {d m : Nat}
    (i : Fin d) (hi : i.val = d - 1)
    (w : PrefixCountRootState d m) :
    prefixCountRootStep d m i w = w := by
  funext j
  have hij : ¬(i : Nat) = j := by
    intro h
    have hj : j.val < d - 1 := j.isLt
    omega
  simp [prefixCountRootStep, hij]

theorem prefixCountRootStepInv_eq_self_of_last {d m : Nat}
    (i : Fin d) (hi : i.val = d - 1)
    (w : PrefixCountRootState d m) :
    prefixCountRootStepInv d m i w = w := by
  funext j
  have hij : ¬(i : Nat) = j := by
    intro h
    have hj : j.val < d - 1 := j.isLt
    omega
  simp [prefixCountRootStepInv, hij]

theorem prefixCountRootStepInv_apply_step {d m : Nat}
    (i : Fin d) (w : PrefixCountRootState d m) :
    prefixCountRootStepInv d m i (prefixCountRootStep d m i w) = w := by
  funext j
  by_cases hij : (i : Nat) = j
  · simp [prefixCountRootStepInv, prefixCountRootStep, hij,
      sub_eq_add_neg, add_assoc]
  · simp [prefixCountRootStepInv, prefixCountRootStep, hij]

theorem prefixCountRootStep_apply_inv {d m : Nat}
    (i : Fin d) (w : PrefixCountRootState d m) :
    prefixCountRootStep d m i (prefixCountRootStepInv d m i w) = w := by
  funext j
  by_cases hij : (i : Nat) = j
  · simp [prefixCountRootStepInv, prefixCountRootStep, hij,
      sub_eq_add_neg, add_assoc]
  · simp [prefixCountRootStepInv, prefixCountRootStep, hij]

theorem prefixCountRootStep_apply_zero {d m : Nat} (hd2 : 2 ≤ d)
    (i : Fin d) (w : PrefixCountRootState d m) :
    prefixCountRootStep d m i w ⟨0, by omega⟩ =
      if i.val = 0 then w ⟨0, by omega⟩ + 1 else w ⟨0, by omega⟩ := by
  by_cases hi : i.val = 0
  · simp [prefixCountRootStep, hi]
  · simp [prefixCountRootStep, hi]

theorem prefixCountRootStep_apply_coord {d m : Nat}
    (i : Fin d) (w : PrefixCountRootState d m) (j : Fin (d - 1)) :
    prefixCountRootStep d m i w j =
      if i.val = j.val then w j + 1 else w j := by
  by_cases hij : i.val = j.val
  · simp [prefixCountRootStep, hij]
  · simp [prefixCountRootStep, hij]

theorem prefixCountRootStep_eq_succ_cast {d m : Nat} (hd1 : 1 ≤ d)
    (i : Fin d) (w : PrefixCountRootState d m) :
    prefixCountRootStep d m i w =
      prefixCountRootStepSucc
        ((finCongr (Nat.sub_add_cancel hd1)).symm i) w := by
  funext j
  rw [prefixCountRootStep, prefixCountRootStepSucc]
  by_cases hcast :
      (finCongr (Nat.sub_add_cancel hd1)).symm i = j.castSucc
  · have hval : (i : Nat) = j := by
      have := congrArg Fin.val hcast
      simpa using this
    have hcast' :
        Fin.cast (Nat.sub_add_cancel hd1).symm i = j.castSucc := by
      simpa using hcast
    simp [hcast', hval]
  · have hval : ¬ (i : Nat) = j := by
      intro hv
      apply hcast
      ext
      simp [hv]
    have hcast' :
        ¬ Fin.cast (Nat.sub_add_cancel hd1).symm i = j.castSucc := by
      intro h
      exact hcast (by simpa using h)
    simp [hcast', hval]

theorem prefixCountRootStepSucc_bijective {n m : Nat}
    (i : Fin (n + 1)) :
    Function.Bijective (prefixCountRootStepSucc (m := m) i) := by
  constructor
  · intro w v h
    funext j
    have hj := congrFun h j
    by_cases hij : i = j.castSucc
    · have hj' := congrArg (fun x : ZMod m => x - 1) hj
      simpa [prefixCountRootStepSucc, hij, sub_eq_add_neg, add_assoc] using hj'
    · simpa [prefixCountRootStepSucc, hij] using hj
  · intro v
    refine ⟨fun j => if i = j.castSucc then v j - 1 else v j, ?_⟩
    funext j
    by_cases hij : i = j.castSucc
    · simp [prefixCountRootStepSucc, hij, sub_eq_add_neg, add_assoc]
    · simp [prefixCountRootStepSucc, hij]

theorem prefixCountRootStep_bijective {d m : Nat}
    (i : Fin d) :
    Function.Bijective (prefixCountRootStep d m i) := by
  have hdpos : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hd1 : 1 ≤ d := Nat.succ_le_iff.mpr hdpos
  let e := (finCongr (Nat.sub_add_cancel hd1)).symm i
  have hfun : prefixCountRootStep d m i = prefixCountRootStepSucc e := by
    funext w
    exact prefixCountRootStep_eq_succ_cast hd1 i w
  simpa [hfun] using prefixCountRootStepSucc_bijective (m := m) e

def prefixCountRootStateHeadTailEquiv (d m : Nat) (hd2 : 2 ≤ d) :
    PrefixCountRootState d m ≃ ZMod m × (Fin (d - 2) → ZMod m) where
  toFun w := (w ⟨0, by omega⟩, fun j => w ⟨j.val + 1, by omega⟩)
  invFun x := fun j =>
    if hj0 : j.val = 0 then x.1 else x.2 ⟨j.val - 1, by omega⟩
  left_inv := by
    intro w
    funext j
    by_cases hj0 : j.val = 0
    · have hj : j = ⟨0, by omega⟩ := by
        apply Fin.ext
        exact hj0
      rw [hj]
      simp
    · have hidx :
          (⟨(j.val - 1) + 1, by omega⟩ : Fin (d - 1)) = j := by
        apply Fin.ext
        simp
        omega
      simp [hj0, hidx]
  right_inv := by
    intro x
    ext j
    · simp
    · have hne : ¬j.val + 1 = 0 := by omega
      have hidx :
          (⟨(j.val + 1) - 1, by omega⟩ : Fin (d - 2)) = j := by
        apply Fin.ext
        simp
      simp [hne, hidx]

@[simp] theorem prefixCountRootStateHeadTailEquiv_fst
    {d m : Nat} (hd2 : 2 ≤ d) (w : PrefixCountRootState d m) :
    (prefixCountRootStateHeadTailEquiv d m hd2 w).1 = w ⟨0, by omega⟩ :=
  rfl

@[simp] theorem prefixCountRootStateHeadTailEquiv_snd
    {d m : Nat} (hd2 : 2 ≤ d) (w : PrefixCountRootState d m)
    (j : Fin (d - 2)) :
    (prefixCountRootStateHeadTailEquiv d m hd2 w).2 j =
      w ⟨j.val + 1, by omega⟩ :=
  rfl

@[simp] theorem prefixCountRootStateHeadTailEquiv_symm_zero
    {d m : Nat} (hd2 : 2 ≤ d)
    (x : ZMod m × (Fin (d - 2) → ZMod m)) :
    (prefixCountRootStateHeadTailEquiv d m hd2).symm x ⟨0, by omega⟩ =
      x.1 := by
  simp [prefixCountRootStateHeadTailEquiv]

@[simp] theorem prefixCountRootStateHeadTailEquiv_symm_succ
    {d m : Nat} (hd2 : 2 ≤ d)
    (x : ZMod m × (Fin (d - 2) → ZMod m)) (j : Fin (d - 2)) :
    (prefixCountRootStateHeadTailEquiv d m hd2).symm x
        ⟨j.val + 1, by omega⟩ =
      x.2 j := by
  have hne : ¬j.val + 1 = 0 := by omega
  have hidx :
      (⟨(j.val + 1) - 1, by omega⟩ : Fin (d - 2)) = j := by
    apply Fin.ext
    simp
  simp [prefixCountRootStateHeadTailEquiv, hne, hidx]

/--
The canonical prefix-count symbol permutation associated to a positive
stop-rank `rho`.  It fixes `0`, sends `1` to `rho`, shifts `2,...,rho` down by
one, and fixes all symbols above `rho`.
-/
def prefixCountLambdaRho (d : Nat) (rho : Fin d) (s : Fin d) : Fin d :=
  if _hs0 : s.val = 0 then
    ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le rho.val) rho.isLt⟩
  else if _hs1 : s.val = 1 then
    rho
  else if _hlt : rho.val < s.val then
    s
  else
    ⟨s.val - 1, by omega⟩

theorem prefixCountLambdaRho_eq_self_of_val_zero
    {d : Nat} (rho : Fin d) {s : Fin d} (hs : s.val = 0) :
    prefixCountLambdaRho d rho s = s := by
  ext
  simp [prefixCountLambdaRho, hs]

theorem prefixCountLambdaRho_eq_rho_of_val_one
    {d : Nat} (rho : Fin d) {s : Fin d} (hs : s.val = 1) :
    prefixCountLambdaRho d rho s = rho := by
  ext
  simp [prefixCountLambdaRho, hs]

theorem prefixCountLambdaRho_eq_self_of_rho_lt
    {d : Nat} (rho : Fin d) {s : Fin d}
    (hs0 : s.val ≠ 0) (hs1 : s.val ≠ 1)
    (hlt : rho.val < s.val) :
    prefixCountLambdaRho d rho s = s := by
  ext
  simp [prefixCountLambdaRho, hs0, hs1, hlt]

theorem prefixCountLambdaRho_val_eq_pred
    {d : Nat} (rho : Fin d) {s : Fin d}
    (hs0 : s.val ≠ 0) (hs1 : s.val ≠ 1)
    (hlt : ¬rho.val < s.val) :
    (prefixCountLambdaRho d rho s).val = s.val - 1 := by
  simp [prefixCountLambdaRho, hs0, hs1, hlt]

theorem prefixCountLambdaRho_eq_pred
    {d : Nat} (rho : Fin d) {s : Fin d}
    (hs0 : s.val ≠ 0) (hs1 : s.val ≠ 1)
    (hlt : ¬rho.val < s.val) :
    prefixCountLambdaRho d rho s =
      ⟨s.val - 1, by omega⟩ := by
  ext
  exact prefixCountLambdaRho_val_eq_pred rho hs0 hs1 hlt

theorem prefixCountLambdaRho_val_eq_zero_iff
    {d : Nat} (rho : Fin d) {s : Fin d}
    (hrho : rho.val ≠ 0) :
    (prefixCountLambdaRho d rho s).val = 0 ↔ s.val = 0 := by
  constructor
  · intro h
    by_cases hs0 : s.val = 0
    · exact hs0
    · by_cases hs1 : s.val = 1
      · have hval : (prefixCountLambdaRho d rho s).val = rho.val := by
          rw [prefixCountLambdaRho_eq_rho_of_val_one rho hs1]
        exact False.elim (hrho (hval ▸ h))
      · by_cases hlt : rho.val < s.val
        · have hval : prefixCountLambdaRho d rho s = s :=
            prefixCountLambdaRho_eq_self_of_rho_lt rho hs0 hs1 hlt
          exact hval.symm ▸ h
        · have hval :
            (prefixCountLambdaRho d rho s).val = s.val - 1 :=
            prefixCountLambdaRho_val_eq_pred rho hs0 hs1 hlt
          have hsge : 2 ≤ s.val := by omega
          omega
  · intro hs
    simpa [hs] using
      congrArg Fin.val (prefixCountLambdaRho_eq_self_of_val_zero rho hs)

theorem prefixCountLambdaRho_val_eq_pos_iff
    {d : Nat} (rho s : Fin d) {l : Nat} (hl : 0 < l) :
    (prefixCountLambdaRho d rho s).val = l ↔
      (s.val = 1 ∧ rho.val = l) ∨
        (s.val = l ∧ 1 < s.val ∧ rho.val < s.val) ∨
        (s.val = l + 1 ∧ ¬ rho.val < s.val) := by
  unfold prefixCountLambdaRho
  by_cases hs0 : s.val = 0
  · simp [hs0]
    omega
  · by_cases hs1 : s.val = 1
    · simp [hs0, hs1]
    · by_cases hlt : rho.val < s.val
      · simp [hs0, hs1, hlt]
        omega
      · simp [hs0, hs1, hlt]
        omega

def prefixCountLambdaRhoInv (d : Nat) (rho : Fin d) (s : Fin d) : Fin d :=
  if _hs0 : s.val = 0 then
    ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le rho.val) rho.isLt⟩
  else if _hlt : s.val < rho.val then
    ⟨s.val + 1, by omega⟩
  else if _heq : s.val = rho.val then
    ⟨1, by omega⟩
  else
    s

theorem prefixCountLambdaRhoInv_apply_lambda
    {d : Nat} (rho : Fin d) (hrho : rho.val ≠ 0) :
    ∀ s : Fin d,
      prefixCountLambdaRhoInv d rho
          (prefixCountLambdaRho d rho s) = s := by
  intro s
  unfold prefixCountLambdaRho prefixCountLambdaRhoInv
  by_cases hs0 : s.val = 0
  · ext
    simp [hs0]
  · by_cases hs1 : s.val = 1
    · ext
      simp [hs1, hrho]
    · by_cases hlt : rho.val < s.val
      · ext
        have hnot_lt : ¬s.val < rho.val := by omega
        have hne : s.val ≠ rho.val := by omega
        simp [hs0, hs1, hlt, hnot_lt, hne]
      · ext
        have hs_ge_two : 2 ≤ s.val := by omega
        have hpred_ne_zero : s.val - 1 ≠ 0 := by omega
        have hpred_lt : s.val - 1 < rho.val := by omega
        simp [hs0, hs1, hlt, hpred_ne_zero, hpred_lt]
        omega

theorem prefixCountLambdaRho_apply_inv
    {d : Nat} (rho : Fin d) (hrho : rho.val ≠ 0) :
    ∀ s : Fin d,
      prefixCountLambdaRho d rho
          (prefixCountLambdaRhoInv d rho s) = s := by
  intro s
  unfold prefixCountLambdaRho prefixCountLambdaRhoInv
  by_cases hs0 : s.val = 0
  · ext
    simp [hs0]
  · by_cases hlt : s.val < rho.val
    · ext
      have hnot_rho_lt_succ : ¬rho.val < s.val + 1 := by omega
      simp [hs0, hlt, hnot_rho_lt_succ]
    · by_cases heq : s.val = rho.val
      · ext
        simp [heq, hrho]
      · ext
        have hrho_lt : rho.val < s.val := by omega
        have hs_ne_one : s.val ≠ 1 := by omega
        simp [hs0, hlt, heq, hrho_lt, hs_ne_one]

theorem prefixCountLambdaRho_bijective
    {d : Nat} (rho : Fin d) (hrho : rho.val ≠ 0) :
    Function.Bijective (prefixCountLambdaRho d rho) := by
  constructor
  · intro a b hab
    have h := congrArg (prefixCountLambdaRhoInv d rho) hab
    simpa [prefixCountLambdaRhoInv_apply_lambda rho hrho] using h
  · intro s
    refine ⟨prefixCountLambdaRhoInv d rho s, ?_⟩
    exact prefixCountLambdaRho_apply_inv rho hrho s

def prefixCountLayerIndex {m : Nat} [NeZero m] (t : ZMod m) : Fin m :=
  ⟨t.val, ZMod.val_lt t⟩

theorem prefixCountLayerIndex_natCast_of_lt {m : Nat} [NeZero m]
    {t : Nat} (ht : t < m) :
    prefixCountLayerIndex ((t : Nat) : ZMod m) = ⟨t, ht⟩ := by
  ext
  simp [prefixCountLayerIndex, ZMod.val_natCast, Nat.mod_eq_of_lt ht]

theorem prefixCountLayerIndex_natCast_val {m : Nat} [NeZero m]
    (t : Fin m) :
    prefixCountLayerIndex ((t.val : Nat) : ZMod m) = t := by
  exact prefixCountLayerIndex_natCast_of_lt t.isLt

def prefixCountCanonicalDir {d m : Nat} [NeZero m]
    {M : Matrix (Fin d) (Fin d) Nat}
    (rho : ZMod m → PrefixCountRootState d m → Fin d)
    (L : PrefixCount.LayerPermCounts d m M)
    (t : ZMod m) (w : PrefixCountRootState d m)
    (c : Fin d) : Fin d :=
  prefixCountLambdaRho d (rho t w) (L.layer (prefixCountLayerIndex t) c)

theorem prefixCountCanonicalDir_bijective {d m : Nat} [NeZero m]
    {M : Matrix (Fin d) (Fin d) Nat}
    (rho : ZMod m → PrefixCountRootState d m → Fin d)
    (hrho : ∀ t w, (rho t w).val ≠ 0)
    (L : PrefixCount.LayerPermCounts d m M) :
    ∀ t w, Function.Bijective (prefixCountCanonicalDir rho L t w) := by
  intro t w
  exact (prefixCountLambdaRho_bijective (rho t w) (hrho t w)).comp
    (L.layer (prefixCountLayerIndex t)).bijective

def prefixCountCanonicalSchedule {d m : Nat} [NeZero m]
    {M : Matrix (Fin d) (Fin d) Nat}
    (rho : ZMod m → PrefixCountRootState d m → Fin d)
    (L : PrefixCount.LayerPermCounts d m M) :
    Shared.RootFlatSchedule (Fin d) (Fin d) (PrefixCountRootState d m) m where
  dir := prefixCountCanonicalDir rho L
  step := prefixCountRootStep d m

theorem prefixCountCanonicalSchedule_rowLatin {d m : Nat} [NeZero m]
    {M : Matrix (Fin d) (Fin d) Nat}
    (rho : ZMod m → PrefixCountRootState d m → Fin d)
    (hrho : ∀ t w, (rho t w).val ≠ 0)
    (L : PrefixCount.LayerPermCounts d m M) :
    (prefixCountCanonicalSchedule rho L).rowLatin := by
  intro t w
  exact prefixCountCanonicalDir_bijective rho hrho L t w

theorem prefixCountCanonicalSchedule_step {d m : Nat} [NeZero m]
    {M : Matrix (Fin d) (Fin d) Nat}
    (rho : ZMod m → PrefixCountRootState d m → Fin d)
    (L : PrefixCount.LayerPermCounts d m M) :
    (prefixCountCanonicalSchedule rho L).step = prefixCountRootStep d m := rfl

def prefixCountCanonicalRhoHit {d m : Nat}
    (t : ZMod m) (w : PrefixCountRootState d m)
    (j : Fin (d - 1)) : Prop :=
  j.val + 1 < d - 1 ∧ w j = t

def prefixCountCanonicalRhoHitNat {d m : Nat}
    (t : ZMod m) (w : PrefixCountRootState d m)
    (j : Nat) : Prop :=
  ∃ hj : j < d - 1,
    j + 1 < d - 1 ∧ w ⟨j, hj⟩ = t

theorem prefixCountCanonicalRhoHitNat_of_fin
    {d m : Nat} {t : ZMod m} {w : PrefixCountRootState d m}
    {j : Fin (d - 1)}
    (h : prefixCountCanonicalRhoHit t w j) :
    prefixCountCanonicalRhoHitNat t w j.val :=
  ⟨j.isLt, h⟩

theorem prefixCountCanonicalRhoHit_of_nat
    {d m : Nat} {t : ZMod m} {w : PrefixCountRootState d m}
    {j : Nat} (h : prefixCountCanonicalRhoHitNat t w j)
    {hj : j < d - 1} :
    prefixCountCanonicalRhoHit t w ⟨j, hj⟩ := by
  rcases h with ⟨hj', hlt, hw⟩
  constructor
  · exact hlt
  · convert hw

theorem prefixCountCanonicalRhoHitNat_rootStep_iff_of_ne
    {d m : Nat} {t : ZMod m} {w : PrefixCountRootState d m}
    {i : Fin d} {j : Nat} (hij : i.val ≠ j) :
    prefixCountCanonicalRhoHitNat t (prefixCountRootStep d m i w) j ↔
      prefixCountCanonicalRhoHitNat t w j := by
  constructor
  · intro h
    rcases h with ⟨hj, hlt, hw⟩
    refine ⟨hj, hlt, ?_⟩
    simpa [prefixCountRootStep, hij] using hw
  · intro h
    rcases h with ⟨hj, hlt, hw⟩
    refine ⟨hj, hlt, ?_⟩
    simpa [prefixCountRootStep, hij] using hw

theorem prefixCountCanonicalRhoHitNat_rootStepInv_iff_of_ne
    {d m : Nat} {t : ZMod m} {w : PrefixCountRootState d m}
    {i : Fin d} {j : Nat} (hij : i.val ≠ j) :
    prefixCountCanonicalRhoHitNat t (prefixCountRootStepInv d m i w) j ↔
      prefixCountCanonicalRhoHitNat t w j := by
  constructor
  · intro h
    rcases h with ⟨hj, hlt, hw⟩
    refine ⟨hj, hlt, ?_⟩
    simpa [prefixCountRootStepInv, hij] using hw
  · intro h
    rcases h with ⟨hj, hlt, hw⟩
    refine ⟨hj, hlt, ?_⟩
    simpa [prefixCountRootStepInv, hij] using hw

noncomputable def prefixCountCanonicalRhoFirstNat
    {d m : Nat} (t : ZMod m) (w : PrefixCountRootState d m)
    (h : ∃ j : Nat, prefixCountCanonicalRhoHitNat t w j) : Nat := by
  classical
  exact Nat.find h

theorem prefixCountCanonicalRhoFirstNat_spec
    {d m : Nat} {t : ZMod m} {w : PrefixCountRootState d m}
    (h : ∃ j : Nat, prefixCountCanonicalRhoHitNat t w j) :
    prefixCountCanonicalRhoHitNat t w
      (prefixCountCanonicalRhoFirstNat t w h) := by
  classical
  unfold prefixCountCanonicalRhoFirstNat
  exact Nat.find_spec h

theorem prefixCountCanonicalRhoFirstNat_minimal
    {d m : Nat} {t : ZMod m} {w : PrefixCountRootState d m}
    (h : ∃ j : Nat, prefixCountCanonicalRhoHitNat t w j)
    {j : Nat} (hj : prefixCountCanonicalRhoHitNat t w j) :
    prefixCountCanonicalRhoFirstNat t w h ≤ j := by
  classical
  unfold prefixCountCanonicalRhoFirstNat
  exact Nat.find_min' h hj

noncomputable def prefixCountCanonicalRho (d m : Nat) (hd2 : 2 ≤ d)
    (t : ZMod m) (w : PrefixCountRootState d m) : Fin d := by
  classical
  exact
    if h : ∃ j : Nat, prefixCountCanonicalRhoHitNat t w j then
      ⟨prefixCountCanonicalRhoFirstNat t w h + 1, by
        rcases prefixCountCanonicalRhoFirstNat_spec h with ⟨hj, hlt, hw⟩
        omega⟩
    else
      ⟨d - 1, by omega⟩

theorem prefixCountCanonicalRho_ne_zero {d m : Nat} (hd2 : 2 ≤ d)
    (t : ZMod m) (w : PrefixCountRootState d m) :
    (prefixCountCanonicalRho d m hd2 t w).val ≠ 0 := by
  unfold prefixCountCanonicalRho
  classical
  by_cases h : ∃ j : Nat, prefixCountCanonicalRhoHitNat t w j
  · simp [h]
  · have hpos : d - 1 ≠ 0 := by omega
    simpa [h] using hpos

theorem prefixCountCanonicalRho_find_hit
    {d m : Nat} {t : ZMod m} {w : PrefixCountRootState d m}
    (h : ∃ j : Nat, prefixCountCanonicalRhoHitNat t w j) :
    prefixCountCanonicalRhoHitNat t w
      (prefixCountCanonicalRhoFirstNat t w h) :=
  prefixCountCanonicalRhoFirstNat_spec h

theorem prefixCountCanonicalRho_val_eq_find_succ
    {d m : Nat} (hd2 : 2 ≤ d)
    {t : ZMod m} {w : PrefixCountRootState d m}
    (h : ∃ j : Nat, prefixCountCanonicalRhoHitNat t w j) :
    (prefixCountCanonicalRho d m hd2 t w).val =
      prefixCountCanonicalRhoFirstNat t w h + 1 := by
  classical
  unfold prefixCountCanonicalRho
  simp [h]

theorem prefixCountCanonicalRho_minimal
    {d m : Nat} (hd2 : 2 ≤ d)
    {t : ZMod m} {w : PrefixCountRootState d m}
    (h : ∃ j : Nat, prefixCountCanonicalRhoHitNat t w j)
    {j : Nat} (hj : prefixCountCanonicalRhoHitNat t w j) :
    (prefixCountCanonicalRho d m hd2 t w).val ≤ j + 1 := by
  classical
  rw [prefixCountCanonicalRho_val_eq_find_succ hd2 h]
  exact Nat.succ_le_succ (prefixCountCanonicalRhoFirstNat_minimal h hj)

theorem prefixCountCanonicalRho_eq_last_of_no_hit
    {d m : Nat} (hd2 : 2 ≤ d)
    {t : ZMod m} {w : PrefixCountRootState d m}
    (h : ¬ ∃ j : Nat, prefixCountCanonicalRhoHitNat t w j) :
    prefixCountCanonicalRho d m hd2 t w = ⟨d - 1, by omega⟩ := by
  classical
  unfold prefixCountCanonicalRho
  simp [h]

theorem prefixCountCanonicalRho_no_hit_before
    {d m : Nat} (hd2 : 2 ≤ d)
    {t : ZMod m} {w : PrefixCountRootState d m}
    {j : Nat}
    (hj : j + 1 < (prefixCountCanonicalRho d m hd2 t w).val) :
    ¬ prefixCountCanonicalRhoHitNat t w j := by
  intro hhit
  by_cases h : ∃ k : Nat, prefixCountCanonicalRhoHitNat t w k
  · have hmin := prefixCountCanonicalRho_minimal hd2 h hhit
    omega
  · exact h ⟨j, hhit⟩

theorem prefixCountCanonicalRho_no_fin_hit_before
    {d m : Nat} (hd2 : 2 ≤ d)
    {t : ZMod m} {w : PrefixCountRootState d m}
    {j : Fin (d - 1)}
    (hj : j.val + 1 < (prefixCountCanonicalRho d m hd2 t w).val) :
    ¬ prefixCountCanonicalRhoHit t w j := by
  intro hhit
  exact prefixCountCanonicalRho_no_hit_before hd2 hj
    (prefixCountCanonicalRhoHitNat_of_fin hhit)

theorem prefixCountCanonicalRho_pred_hitNat
    {d m : Nat} (hd2 : 2 ≤ d)
    {t : ZMod m} {w : PrefixCountRootState d m}
    (hrho : (prefixCountCanonicalRho d m hd2 t w).val < d - 1) :
    prefixCountCanonicalRhoHitNat t w
      ((prefixCountCanonicalRho d m hd2 t w).val - 1) := by
  by_cases h : ∃ j : Nat, prefixCountCanonicalRhoHitNat t w j
  · have hval := prefixCountCanonicalRho_val_eq_find_succ hd2 h
    have hpred :
        (prefixCountCanonicalRho d m hd2 t w).val - 1 =
          prefixCountCanonicalRhoFirstNat t w h := by
      omega
    simpa [hpred] using prefixCountCanonicalRhoFirstNat_spec h
  · have hlast :
        (prefixCountCanonicalRho d m hd2 t w).val = d - 1 := by
      simpa using congrArg Fin.val
        (prefixCountCanonicalRho_eq_last_of_no_hit hd2 h)
    omega

theorem prefixCountCanonicalRho_pred_hit
    {d m : Nat} (hd2 : 2 ≤ d)
    {t : ZMod m} {w : PrefixCountRootState d m}
    (hrho : (prefixCountCanonicalRho d m hd2 t w).val < d - 1) :
    prefixCountCanonicalRhoHit t w
      ⟨(prefixCountCanonicalRho d m hd2 t w).val - 1, by omega⟩ := by
  exact prefixCountCanonicalRhoHit_of_nat
    (prefixCountCanonicalRho_pred_hitNat hd2 hrho)

theorem prefixCountCanonicalRho_rootStep_self
    {d m : Nat} (hd2 : 2 ≤ d)
    (t : ZMod m) (w : PrefixCountRootState d m) :
    prefixCountCanonicalRho d m hd2 t
        (prefixCountRootStep d m
          (prefixCountCanonicalRho d m hd2 t w) w)
      =
    prefixCountCanonicalRho d m hd2 t w := by
  let rho := prefixCountCanonicalRho d m hd2 t w
  by_cases hlast : rho.val = d - 1
  · have hstep :
        prefixCountRootStep d m rho w = w :=
      prefixCountRootStep_eq_self_of_last rho hlast w
    simp [rho, hstep]
  · have hrho : rho.val < d - 1 := by
      have hrho_lt : rho.val < d := rho.isLt
      omega
    have hhit :
        prefixCountCanonicalRhoHitNat t w (rho.val - 1) := by
      simpa [rho] using
        (prefixCountCanonicalRho_pred_hitNat
          (d := d) (m := m) hd2 (t := t) (w := w) (by simpa [rho] using hrho))
    have hne_moved : rho.val ≠ rho.val - 1 := by
      have hnonzero : rho.val ≠ 0 := by
        simpa [rho] using prefixCountCanonicalRho_ne_zero hd2 t w
      omega
    have hhit' :
        prefixCountCanonicalRhoHitNat t
          (prefixCountRootStep d m rho w) (rho.val - 1) :=
      (prefixCountCanonicalRhoHitNat_rootStep_iff_of_ne
        (d := d) (m := m) (t := t) (w := w)
        (i := rho) (j := rho.val - 1) hne_moved).2 hhit
    have hex' :
        ∃ j : Nat,
          prefixCountCanonicalRhoHitNat t
            (prefixCountRootStep d m rho w) j :=
      ⟨rho.val - 1, hhit'⟩
    have hle :
        (prefixCountCanonicalRho d m hd2 t
          (prefixCountRootStep d m rho w)).val ≤ rho.val := by
      have hmin :=
        prefixCountCanonicalRho_minimal
          (d := d) (m := m) hd2 (t := t)
          (w := prefixCountRootStep d m rho w) hex' hhit'
      omega
    have hnotlt :
        ¬ (prefixCountCanonicalRho d m hd2 t
          (prefixCountRootStep d m rho w)).val < rho.val := by
      intro hlt
      let rho' :=
        prefixCountCanonicalRho d m hd2 t
          (prefixCountRootStep d m rho w)
      have hrho' : rho'.val < d - 1 := by
        have : rho'.val < rho.val := hlt
        omega
      have hhit_pred' :
          prefixCountCanonicalRhoHitNat t
            (prefixCountRootStep d m rho w) (rho'.val - 1) := by
        simpa [rho'] using
          (prefixCountCanonicalRho_pred_hitNat
            (d := d) (m := m) hd2 (t := t)
            (w := prefixCountRootStep d m rho w) hrho')
      have hne' : rho.val ≠ rho'.val - 1 := by omega
      have hhit_pred :
          prefixCountCanonicalRhoHitNat t w (rho'.val - 1) :=
        (prefixCountCanonicalRhoHitNat_rootStep_iff_of_ne
          (d := d) (m := m) (t := t) (w := w)
          (i := rho) (j := rho'.val - 1) hne').1 hhit_pred'
      have hbefore : (rho'.val - 1) + 1 < rho.val := by
        have hnonzero' : rho'.val ≠ 0 := by
          simpa [rho'] using
            prefixCountCanonicalRho_ne_zero
              (d := d) (m := m) hd2 t (prefixCountRootStep d m rho w)
        omega
      exact
        (prefixCountCanonicalRho_no_hit_before
          (d := d) (m := m) hd2 (t := t) (w := w) hbefore)
          hhit_pred
    apply Fin.ext
    have hge :
        rho.val ≤
          (prefixCountCanonicalRho d m hd2 t
            (prefixCountRootStep d m rho w)).val := by
      omega
    exact Nat.le_antisymm hle hge

theorem prefixCountCanonicalRho_rootStepInv_self
    {d m : Nat} (hd2 : 2 ≤ d)
    (t : ZMod m) (w : PrefixCountRootState d m) :
    prefixCountCanonicalRho d m hd2 t
        (prefixCountRootStepInv d m
          (prefixCountCanonicalRho d m hd2 t w) w)
      =
    prefixCountCanonicalRho d m hd2 t w := by
  let rho := prefixCountCanonicalRho d m hd2 t w
  by_cases hlast : rho.val = d - 1
  · have hstep :
        prefixCountRootStepInv d m rho w = w :=
      prefixCountRootStepInv_eq_self_of_last rho hlast w
    simp [rho, hstep]
  · have hrho : rho.val < d - 1 := by
      have hrho_lt : rho.val < d := rho.isLt
      omega
    have hhit :
        prefixCountCanonicalRhoHitNat t w (rho.val - 1) := by
      simpa [rho] using
        (prefixCountCanonicalRho_pred_hitNat
          (d := d) (m := m) hd2 (t := t) (w := w) (by simpa [rho] using hrho))
    have hne_moved : rho.val ≠ rho.val - 1 := by
      have hnonzero : rho.val ≠ 0 := by
        simpa [rho] using prefixCountCanonicalRho_ne_zero hd2 t w
      omega
    have hhit' :
        prefixCountCanonicalRhoHitNat t
          (prefixCountRootStepInv d m rho w) (rho.val - 1) :=
      (prefixCountCanonicalRhoHitNat_rootStepInv_iff_of_ne
        (d := d) (m := m) (t := t) (w := w)
        (i := rho) (j := rho.val - 1) hne_moved).2 hhit
    have hex' :
        ∃ j : Nat,
          prefixCountCanonicalRhoHitNat t
            (prefixCountRootStepInv d m rho w) j :=
      ⟨rho.val - 1, hhit'⟩
    have hle :
        (prefixCountCanonicalRho d m hd2 t
          (prefixCountRootStepInv d m rho w)).val ≤ rho.val := by
      have hmin :=
        prefixCountCanonicalRho_minimal
          (d := d) (m := m) hd2 (t := t)
          (w := prefixCountRootStepInv d m rho w) hex' hhit'
      omega
    have hnotlt :
        ¬ (prefixCountCanonicalRho d m hd2 t
          (prefixCountRootStepInv d m rho w)).val < rho.val := by
      intro hlt
      let rho' :=
        prefixCountCanonicalRho d m hd2 t
          (prefixCountRootStepInv d m rho w)
      have hrho' : rho'.val < d - 1 := by
        have : rho'.val < rho.val := hlt
        omega
      have hhit_pred' :
          prefixCountCanonicalRhoHitNat t
            (prefixCountRootStepInv d m rho w) (rho'.val - 1) := by
        simpa [rho'] using
          (prefixCountCanonicalRho_pred_hitNat
            (d := d) (m := m) hd2 (t := t)
            (w := prefixCountRootStepInv d m rho w) hrho')
      have hne' : rho.val ≠ rho'.val - 1 := by omega
      have hhit_pred :
          prefixCountCanonicalRhoHitNat t w (rho'.val - 1) :=
        (prefixCountCanonicalRhoHitNat_rootStepInv_iff_of_ne
          (d := d) (m := m) (t := t) (w := w)
          (i := rho) (j := rho'.val - 1) hne').1 hhit_pred'
      have hbefore : (rho'.val - 1) + 1 < rho.val := by
        have hnonzero' : rho'.val ≠ 0 := by
          simpa [rho'] using
            prefixCountCanonicalRho_ne_zero
              (d := d) (m := m) hd2 t (prefixCountRootStepInv d m rho w)
        omega
      exact
        (prefixCountCanonicalRho_no_hit_before
          (d := d) (m := m) hd2 (t := t) (w := w) hbefore)
          hhit_pred
    apply Fin.ext
    have hge :
        rho.val ≤
          (prefixCountCanonicalRho d m hd2 t
            (prefixCountRootStepInv d m rho w)).val := by
      omega
    exact Nat.le_antisymm hle hge

theorem prefixCountCanonicalRho_rootStep_after_first
    {d m : Nat} (hd2 : 2 ≤ d)
    (t : ZMod m) (w : PrefixCountRootState d m)
    {i : Fin d}
    (hi : (prefixCountCanonicalRho d m hd2 t w).val < i.val) :
    prefixCountCanonicalRho d m hd2 t (prefixCountRootStep d m i w) =
      prefixCountCanonicalRho d m hd2 t w := by
  let rho := prefixCountCanonicalRho d m hd2 t w
  have hrho : rho.val < d - 1 := by
    have hi_lt : i.val < d := i.isLt
    omega
  have hhit :
      prefixCountCanonicalRhoHitNat t w (rho.val - 1) := by
    simpa [rho] using
      (prefixCountCanonicalRho_pred_hitNat
        (d := d) (m := m) hd2 (t := t) (w := w) (by simpa [rho] using hrho))
  have hne_moved : i.val ≠ rho.val - 1 := by omega
  have hhit' :
      prefixCountCanonicalRhoHitNat t
        (prefixCountRootStep d m i w) (rho.val - 1) :=
    (prefixCountCanonicalRhoHitNat_rootStep_iff_of_ne
      (d := d) (m := m) (t := t) (w := w)
      (i := i) (j := rho.val - 1) hne_moved).2 hhit
  have hex' :
      ∃ j : Nat,
        prefixCountCanonicalRhoHitNat t
          (prefixCountRootStep d m i w) j :=
    ⟨rho.val - 1, hhit'⟩
  have hle :
      (prefixCountCanonicalRho d m hd2 t
        (prefixCountRootStep d m i w)).val ≤ rho.val := by
    have hmin :=
      prefixCountCanonicalRho_minimal
        (d := d) (m := m) hd2 (t := t)
        (w := prefixCountRootStep d m i w) hex' hhit'
    have hnonzero : rho.val ≠ 0 := by
      simpa [rho] using prefixCountCanonicalRho_ne_zero hd2 t w
    omega
  have hnotlt :
      ¬ (prefixCountCanonicalRho d m hd2 t
        (prefixCountRootStep d m i w)).val < rho.val := by
    intro hlt
    let rho' :=
      prefixCountCanonicalRho d m hd2 t
        (prefixCountRootStep d m i w)
    have hrho' : rho'.val < d - 1 := by
      have : rho'.val < rho.val := hlt
      omega
    have hhit_pred' :
        prefixCountCanonicalRhoHitNat t
          (prefixCountRootStep d m i w) (rho'.val - 1) := by
      simpa [rho'] using
        (prefixCountCanonicalRho_pred_hitNat
          (d := d) (m := m) hd2 (t := t)
          (w := prefixCountRootStep d m i w) hrho')
    have hne' : i.val ≠ rho'.val - 1 := by omega
    have hhit_pred :
        prefixCountCanonicalRhoHitNat t w (rho'.val - 1) :=
      (prefixCountCanonicalRhoHitNat_rootStep_iff_of_ne
        (d := d) (m := m) (t := t) (w := w)
        (i := i) (j := rho'.val - 1) hne').1 hhit_pred'
    have hbefore : (rho'.val - 1) + 1 < rho.val := by
      have hnonzero' : rho'.val ≠ 0 := by
        simpa [rho'] using
          prefixCountCanonicalRho_ne_zero
            (d := d) (m := m) hd2 t (prefixCountRootStep d m i w)
      omega
    exact
      (prefixCountCanonicalRho_no_hit_before
        (d := d) (m := m) hd2 (t := t) (w := w) hbefore)
        hhit_pred
  apply Fin.ext
  have hge :
      rho.val ≤
        (prefixCountCanonicalRho d m hd2 t
          (prefixCountRootStep d m i w)).val := by
    omega
  exact Nat.le_antisymm hle hge

theorem prefixCountCanonicalRho_rootStepInv_after_first
    {d m : Nat} (hd2 : 2 ≤ d)
    (t : ZMod m) (w : PrefixCountRootState d m)
    {i : Fin d}
    (hi : (prefixCountCanonicalRho d m hd2 t w).val < i.val) :
    prefixCountCanonicalRho d m hd2 t (prefixCountRootStepInv d m i w) =
      prefixCountCanonicalRho d m hd2 t w := by
  let rho := prefixCountCanonicalRho d m hd2 t w
  have hrho : rho.val < d - 1 := by
    have hi_lt : i.val < d := i.isLt
    omega
  have hhit :
      prefixCountCanonicalRhoHitNat t w (rho.val - 1) := by
    simpa [rho] using
      (prefixCountCanonicalRho_pred_hitNat
        (d := d) (m := m) hd2 (t := t) (w := w) (by simpa [rho] using hrho))
  have hne_moved : i.val ≠ rho.val - 1 := by omega
  have hhit' :
      prefixCountCanonicalRhoHitNat t
        (prefixCountRootStepInv d m i w) (rho.val - 1) :=
    (prefixCountCanonicalRhoHitNat_rootStepInv_iff_of_ne
      (d := d) (m := m) (t := t) (w := w)
      (i := i) (j := rho.val - 1) hne_moved).2 hhit
  have hex' :
      ∃ j : Nat,
        prefixCountCanonicalRhoHitNat t
          (prefixCountRootStepInv d m i w) j :=
    ⟨rho.val - 1, hhit'⟩
  have hle :
      (prefixCountCanonicalRho d m hd2 t
        (prefixCountRootStepInv d m i w)).val ≤ rho.val := by
    have hmin :=
      prefixCountCanonicalRho_minimal
        (d := d) (m := m) hd2 (t := t)
        (w := prefixCountRootStepInv d m i w) hex' hhit'
    have hnonzero : rho.val ≠ 0 := by
      simpa [rho] using prefixCountCanonicalRho_ne_zero hd2 t w
    omega
  have hnotlt :
      ¬ (prefixCountCanonicalRho d m hd2 t
        (prefixCountRootStepInv d m i w)).val < rho.val := by
    intro hlt
    let rho' :=
      prefixCountCanonicalRho d m hd2 t
        (prefixCountRootStepInv d m i w)
    have hrho' : rho'.val < d - 1 := by
      have : rho'.val < rho.val := hlt
      omega
    have hhit_pred' :
        prefixCountCanonicalRhoHitNat t
          (prefixCountRootStepInv d m i w) (rho'.val - 1) := by
      simpa [rho'] using
        (prefixCountCanonicalRho_pred_hitNat
          (d := d) (m := m) hd2 (t := t)
          (w := prefixCountRootStepInv d m i w) hrho')
    have hne' : i.val ≠ rho'.val - 1 := by omega
    have hhit_pred :
        prefixCountCanonicalRhoHitNat t w (rho'.val - 1) :=
      (prefixCountCanonicalRhoHitNat_rootStepInv_iff_of_ne
        (d := d) (m := m) (t := t) (w := w)
        (i := i) (j := rho'.val - 1) hne').1 hhit_pred'
    have hbefore : (rho'.val - 1) + 1 < rho.val := by
      have hnonzero' : rho'.val ≠ 0 := by
        simpa [rho'] using
          prefixCountCanonicalRho_ne_zero
            (d := d) (m := m) hd2 t (prefixCountRootStepInv d m i w)
      omega
    exact
      (prefixCountCanonicalRho_no_hit_before
        (d := d) (m := m) hd2 (t := t) (w := w) hbefore)
        hhit_pred
  apply Fin.ext
  have hge :
      rho.val ≤
        (prefixCountCanonicalRho d m hd2 t
          (prefixCountRootStepInv d m i w)).val := by
    omega
  exact Nat.le_antisymm hle hge

noncomputable def prefixCountFirstHitCanonicalSchedule
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {M : Matrix (Fin d) (Fin d) Nat}
    (L : PrefixCount.LayerPermCounts d m M) :
    Shared.RootFlatSchedule (Fin d) (Fin d) (PrefixCountRootState d m) m :=
  prefixCountCanonicalSchedule (prefixCountCanonicalRho d m hd2) L

theorem prefixCountFirstHitCanonicalSchedule_rowLatin
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {M : Matrix (Fin d) (Fin d) Nat}
    (L : PrefixCount.LayerPermCounts d m M) :
    (prefixCountFirstHitCanonicalSchedule hd2 L).rowLatin := by
  refine prefixCountCanonicalSchedule_rowLatin
    (prefixCountCanonicalRho d m hd2) ?_ L
  intro t w
  exact prefixCountCanonicalRho_ne_zero hd2 t w

theorem prefixCountFirstHitCanonicalSchedule_step
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {M : Matrix (Fin d) (Fin d) Nat}
    (L : PrefixCount.LayerPermCounts d m M) :
    (prefixCountFirstHitCanonicalSchedule hd2 L).step =
      prefixCountRootStep d m := rfl

noncomputable def prefixCountFirstHitSymbolMap
    {d m : Nat} (hd2 : 2 ≤ d)
    (t : ZMod m) (s : Fin d) :
    PrefixCountRootState d m → PrefixCountRootState d m :=
  fun w =>
    prefixCountRootStep d m
      (prefixCountLambdaRho d (prefixCountCanonicalRho d m hd2 t w) s) w

noncomputable def prefixCountFirstHitSymbolMapInv
    {d m : Nat} (hd2 : 2 ≤ d)
    (t : ZMod m) (s : Fin d) :
    PrefixCountRootState d m → PrefixCountRootState d m :=
  fun w =>
    prefixCountRootStepInv d m
      (prefixCountLambdaRho d (prefixCountCanonicalRho d m hd2 t w) s) w

theorem prefixCountFirstHitSymbolMap_apply_zero
    {d m : Nat} (hd2 : 2 ≤ d)
    (t : ZMod m) (s : Fin d) (w : PrefixCountRootState d m) :
    prefixCountFirstHitSymbolMap hd2 t s w ⟨0, by omega⟩ =
      if s.val = 0 then w ⟨0, by omega⟩ + 1 else w ⟨0, by omega⟩ := by
  unfold prefixCountFirstHitSymbolMap
  rw [prefixCountRootStep_apply_zero hd2]
  have hrho :
      (prefixCountCanonicalRho d m hd2 t w).val ≠ 0 :=
    prefixCountCanonicalRho_ne_zero hd2 t w
  by_cases hs0 : s.val = 0
  · have hLambda :
        (prefixCountLambdaRho d
          (prefixCountCanonicalRho d m hd2 t w) s).val = 0 :=
      (prefixCountLambdaRho_val_eq_zero_iff
        (prefixCountCanonicalRho d m hd2 t w) hrho).2 hs0
    simp [hs0, hLambda]
  · have hLambda :
        (prefixCountLambdaRho d
          (prefixCountCanonicalRho d m hd2 t w) s).val ≠ 0 := by
      intro hzero
      exact hs0
        ((prefixCountLambdaRho_val_eq_zero_iff
          (prefixCountCanonicalRho d m hd2 t w) hrho).1 hzero)
    simp [hs0, hLambda]

theorem prefixCountFirstHitSymbolMap_apply_coord
    {d m : Nat} (hd2 : 2 ≤ d)
    (t : ZMod m) (s : Fin d) (w : PrefixCountRootState d m)
    (j : Fin (d - 1)) :
    prefixCountFirstHitSymbolMap hd2 t s w j =
      if (prefixCountLambdaRho d
          (prefixCountCanonicalRho d m hd2 t w) s).val = j.val
      then w j + 1 else w j := by
  unfold prefixCountFirstHitSymbolMap
  rw [prefixCountRootStep_apply_coord]

theorem prefixCountFirstHitSymbolMap_bijective_of_val_zero
    {d m : Nat} (hd2 : 2 ≤ d)
    (t : ZMod m) {s : Fin d} (hs : s.val = 0) :
    Function.Bijective (prefixCountFirstHitSymbolMap hd2 t s) := by
  have hfun :
      prefixCountFirstHitSymbolMap hd2 t s =
        prefixCountRootStep d m s := by
    funext w
    simp [prefixCountFirstHitSymbolMap,
      prefixCountLambdaRho_eq_self_of_val_zero _ hs]
  rw [hfun]
  exact prefixCountRootStep_bijective s

theorem prefixCountFirstHitSymbolMap_inverseLaw_of_val_zero
    {d m : Nat} (hd2 : 2 ≤ d)
    (t : ZMod m) {s : Fin d} (hs : s.val = 0) :
    Function.LeftInverse
        (prefixCountFirstHitSymbolMapInv hd2 t s)
        (prefixCountFirstHitSymbolMap hd2 t s) ∧
      Function.RightInverse
        (prefixCountFirstHitSymbolMapInv hd2 t s)
        (prefixCountFirstHitSymbolMap hd2 t s) := by
  have hfun :
      prefixCountFirstHitSymbolMap hd2 t s =
        prefixCountRootStep d m s := by
    funext w
    simp [prefixCountFirstHitSymbolMap,
      prefixCountLambdaRho_eq_self_of_val_zero _ hs]
  have hinv :
      prefixCountFirstHitSymbolMapInv hd2 t s =
        prefixCountRootStepInv d m s := by
    funext w
    simp [prefixCountFirstHitSymbolMapInv,
      prefixCountLambdaRho_eq_self_of_val_zero _ hs]
  constructor
  · intro w
    rw [hfun, hinv]
    exact prefixCountRootStepInv_apply_step s w
  · intro w
    rw [hfun, hinv]
    exact prefixCountRootStep_apply_inv s w

theorem prefixCountFirstHitSymbolMap_inverseLaw_of_val_one
    {d m : Nat} (hd2 : 2 ≤ d)
    (t : ZMod m) {s : Fin d} (hs : s.val = 1) :
    Function.LeftInverse
        (prefixCountFirstHitSymbolMapInv hd2 t s)
        (prefixCountFirstHitSymbolMap hd2 t s) ∧
      Function.RightInverse
        (prefixCountFirstHitSymbolMapInv hd2 t s)
        (prefixCountFirstHitSymbolMap hd2 t s) := by
  constructor
  · intro w
    simpa [prefixCountFirstHitSymbolMapInv,
      prefixCountFirstHitSymbolMap,
      prefixCountLambdaRho_eq_rho_of_val_one _ hs,
      prefixCountCanonicalRho_rootStep_self hd2 t w]
      using
        prefixCountRootStepInv_apply_step
          (prefixCountCanonicalRho d m hd2 t w) w
  · intro w
    simpa [prefixCountFirstHitSymbolMapInv,
      prefixCountFirstHitSymbolMap,
      prefixCountLambdaRho_eq_rho_of_val_one _ hs,
      prefixCountCanonicalRho_rootStepInv_self hd2 t w]
      using
        prefixCountRootStep_apply_inv
          (prefixCountCanonicalRho d m hd2 t w) w

theorem prefixCountFirstHitSymbolMap_bijective_of_val_one
    {d m : Nat} (hd2 : 2 ≤ d)
    (t : ZMod m) {s : Fin d} (hs : s.val = 1) :
    Function.Bijective (prefixCountFirstHitSymbolMap hd2 t s) := by
  rcases prefixCountFirstHitSymbolMap_inverseLaw_of_val_one hd2 t hs with
    ⟨hLeft, hRight⟩
  constructor
  · intro x y hxy
    have h := congrArg (prefixCountFirstHitSymbolMapInv hd2 t s) hxy
    calc
      x = prefixCountFirstHitSymbolMapInv hd2 t s
            (prefixCountFirstHitSymbolMap hd2 t s x) := (hLeft x).symm
      _ = prefixCountFirstHitSymbolMapInv hd2 t s
            (prefixCountFirstHitSymbolMap hd2 t s y) := h
      _ = y := hLeft y
  · intro y
    exact ⟨prefixCountFirstHitSymbolMapInv hd2 t s y, hRight y⟩

theorem prefixCountFirstHitSymbolMap_rho_eq_of_rho_lt
    {d m : Nat} (hd2 : 2 ≤ d)
    (t : ZMod m) {s : Fin d} (w : PrefixCountRootState d m)
    (hs0 : s.val ≠ 0) (hs1 : s.val ≠ 1)
    (hlt : (prefixCountCanonicalRho d m hd2 t w).val < s.val) :
    prefixCountCanonicalRho d m hd2 t
        (prefixCountFirstHitSymbolMap hd2 t s w)
      =
    prefixCountCanonicalRho d m hd2 t w := by
  unfold prefixCountFirstHitSymbolMap
  rw [prefixCountLambdaRho_eq_self_of_rho_lt
    (prefixCountCanonicalRho d m hd2 t w) hs0 hs1 hlt]
  exact prefixCountCanonicalRho_rootStep_after_first hd2 t w hlt

theorem prefixCountFirstHitSymbolMapInv_rho_eq_of_rho_lt
    {d m : Nat} (hd2 : 2 ≤ d)
    (t : ZMod m) {s : Fin d} (w : PrefixCountRootState d m)
    (hs0 : s.val ≠ 0) (hs1 : s.val ≠ 1)
    (hlt : (prefixCountCanonicalRho d m hd2 t w).val < s.val) :
    prefixCountCanonicalRho d m hd2 t
        (prefixCountFirstHitSymbolMapInv hd2 t s w)
      =
    prefixCountCanonicalRho d m hd2 t w := by
  unfold prefixCountFirstHitSymbolMapInv
  rw [prefixCountLambdaRho_eq_self_of_rho_lt
    (prefixCountCanonicalRho d m hd2 t w) hs0 hs1 hlt]
  exact prefixCountCanonicalRho_rootStepInv_after_first hd2 t w hlt

theorem prefixCountFirstHitSymbolMapInv_apply_symbolMap_of_rho_lt
    {d m : Nat} (hd2 : 2 ≤ d)
    (t : ZMod m) {s : Fin d} (w : PrefixCountRootState d m)
    (hs0 : s.val ≠ 0) (hs1 : s.val ≠ 1)
    (hlt : (prefixCountCanonicalRho d m hd2 t w).val < s.val) :
    prefixCountFirstHitSymbolMapInv hd2 t s
        (prefixCountFirstHitSymbolMap hd2 t s w) = w := by
  have hrho :=
    prefixCountFirstHitSymbolMap_rho_eq_of_rho_lt
      hd2 t w hs0 hs1 hlt
  unfold prefixCountFirstHitSymbolMapInv prefixCountFirstHitSymbolMap
  rw [prefixCountLambdaRho_eq_self_of_rho_lt
    (prefixCountCanonicalRho d m hd2 t w) hs0 hs1 hlt]
  have hrho' :
      prefixCountCanonicalRho d m hd2 t
          (prefixCountRootStep d m s w)
        =
      prefixCountCanonicalRho d m hd2 t w := by
    simpa [prefixCountFirstHitSymbolMap,
      prefixCountLambdaRho_eq_self_of_rho_lt
        (prefixCountCanonicalRho d m hd2 t w) hs0 hs1 hlt]
      using hrho
  have hlt' :
      (prefixCountCanonicalRho d m hd2 t
        (prefixCountRootStep d m s w)).val < s.val := by
    simpa [hrho'] using hlt
  rw [prefixCountLambdaRho_eq_self_of_rho_lt
    (prefixCountCanonicalRho d m hd2 t
      (prefixCountRootStep d m s w)) hs0 hs1 hlt']
  exact prefixCountRootStepInv_apply_step s w

theorem prefixCountFirstHitSymbolMap_apply_inv_of_rho_lt
    {d m : Nat} (hd2 : 2 ≤ d)
    (t : ZMod m) {s : Fin d} (w : PrefixCountRootState d m)
    (hs0 : s.val ≠ 0) (hs1 : s.val ≠ 1)
    (hlt : (prefixCountCanonicalRho d m hd2 t w).val < s.val) :
    prefixCountFirstHitSymbolMap hd2 t s
        (prefixCountFirstHitSymbolMapInv hd2 t s w) = w := by
  have hrho :=
    prefixCountFirstHitSymbolMapInv_rho_eq_of_rho_lt
      hd2 t w hs0 hs1 hlt
  unfold prefixCountFirstHitSymbolMapInv prefixCountFirstHitSymbolMap
  rw [prefixCountLambdaRho_eq_self_of_rho_lt
    (prefixCountCanonicalRho d m hd2 t w) hs0 hs1 hlt]
  have hrho' :
      prefixCountCanonicalRho d m hd2 t
          (prefixCountRootStepInv d m s w)
        =
      prefixCountCanonicalRho d m hd2 t w := by
    simpa [prefixCountFirstHitSymbolMapInv,
      prefixCountLambdaRho_eq_self_of_rho_lt
        (prefixCountCanonicalRho d m hd2 t w) hs0 hs1 hlt]
      using hrho
  have hlt' :
      (prefixCountCanonicalRho d m hd2 t
        (prefixCountRootStepInv d m s w)).val < s.val := by
    simpa [hrho'] using hlt
  rw [prefixCountLambdaRho_eq_self_of_rho_lt
    (prefixCountCanonicalRho d m hd2 t
      (prefixCountRootStepInv d m s w)) hs0 hs1 hlt']
  exact prefixCountRootStep_apply_inv s w

theorem prefixCountFirstHitSymbolMap_not_rho_lt_of_not_rho_lt
    {d m : Nat} (hd2 : 2 ≤ d)
    (t : ZMod m) {s : Fin d} (w : PrefixCountRootState d m)
    (hs0 : s.val ≠ 0) (hs1 : s.val ≠ 1)
    (hnot : ¬(prefixCountCanonicalRho d m hd2 t w).val < s.val) :
    ¬ (prefixCountCanonicalRho d m hd2 t
        (prefixCountFirstHitSymbolMap hd2 t s w)).val < s.val := by
  intro hlt'
  let i : Fin d := ⟨s.val - 1, by omega⟩
  have hs_ge_two : 2 ≤ s.val := by omega
  have hrho_ge : s.val ≤ (prefixCountCanonicalRho d m hd2 t w).val := by
    omega
  have hmap :
      prefixCountFirstHitSymbolMap hd2 t s w =
        prefixCountRootStep d m i w := by
    unfold prefixCountFirstHitSymbolMap
    rw [prefixCountLambdaRho_eq_pred
      (prefixCountCanonicalRho d m hd2 t w) hs0 hs1 hnot]
  let rho' :=
    prefixCountCanonicalRho d m hd2 t
      (prefixCountFirstHitSymbolMap hd2 t s w)
  have hrho'_lt_last : rho'.val < d - 1 := by
    have : rho'.val < s.val := hlt'
    have hslt : s.val < d := s.isLt
    omega
  have hhit' :
      prefixCountCanonicalRhoHitNat t
        (prefixCountFirstHitSymbolMap hd2 t s w) (rho'.val - 1) := by
    simpa [rho'] using
      (prefixCountCanonicalRho_pred_hitNat
        (d := d) (m := m) hd2 (t := t)
        (w := prefixCountFirstHitSymbolMap hd2 t s w) hrho'_lt_last)
  have hne : i.val ≠ rho'.val - 1 := by
    have hnonzero' : rho'.val ≠ 0 := by
      simpa [rho'] using
        prefixCountCanonicalRho_ne_zero
          (d := d) (m := m) hd2 t
          (prefixCountFirstHitSymbolMap hd2 t s w)
    have hi_val : i.val = s.val - 1 := rfl
    omega
  have hhit :
      prefixCountCanonicalRhoHitNat t w (rho'.val - 1) := by
    rw [hmap] at hhit'
    exact
      (prefixCountCanonicalRhoHitNat_rootStep_iff_of_ne
        (d := d) (m := m) (t := t) (w := w)
        (i := i) (j := rho'.val - 1) hne).1 hhit'
  have hbefore :
      (rho'.val - 1) + 1 <
        (prefixCountCanonicalRho d m hd2 t w).val := by
    have hnonzero' : rho'.val ≠ 0 := by
      simpa [rho'] using
        prefixCountCanonicalRho_ne_zero
          (d := d) (m := m) hd2 t
          (prefixCountFirstHitSymbolMap hd2 t s w)
    omega
  exact
    (prefixCountCanonicalRho_no_hit_before
      (d := d) (m := m) hd2 (t := t) (w := w) hbefore)
      hhit

theorem prefixCountFirstHitSymbolMapInv_not_rho_lt_of_not_rho_lt
    {d m : Nat} (hd2 : 2 ≤ d)
    (t : ZMod m) {s : Fin d} (w : PrefixCountRootState d m)
    (hs0 : s.val ≠ 0) (hs1 : s.val ≠ 1)
    (hnot : ¬(prefixCountCanonicalRho d m hd2 t w).val < s.val) :
    ¬ (prefixCountCanonicalRho d m hd2 t
        (prefixCountFirstHitSymbolMapInv hd2 t s w)).val < s.val := by
  intro hlt'
  let i : Fin d := ⟨s.val - 1, by omega⟩
  have hs_ge_two : 2 ≤ s.val := by omega
  have hrho_ge : s.val ≤ (prefixCountCanonicalRho d m hd2 t w).val := by
    omega
  have hmap :
      prefixCountFirstHitSymbolMapInv hd2 t s w =
        prefixCountRootStepInv d m i w := by
    unfold prefixCountFirstHitSymbolMapInv
    rw [prefixCountLambdaRho_eq_pred
      (prefixCountCanonicalRho d m hd2 t w) hs0 hs1 hnot]
  let rho' :=
    prefixCountCanonicalRho d m hd2 t
      (prefixCountFirstHitSymbolMapInv hd2 t s w)
  have hrho'_lt_last : rho'.val < d - 1 := by
    have : rho'.val < s.val := hlt'
    have hslt : s.val < d := s.isLt
    omega
  have hhit' :
      prefixCountCanonicalRhoHitNat t
        (prefixCountFirstHitSymbolMapInv hd2 t s w) (rho'.val - 1) := by
    simpa [rho'] using
      (prefixCountCanonicalRho_pred_hitNat
        (d := d) (m := m) hd2 (t := t)
        (w := prefixCountFirstHitSymbolMapInv hd2 t s w) hrho'_lt_last)
  have hne : i.val ≠ rho'.val - 1 := by
    have hnonzero' : rho'.val ≠ 0 := by
      simpa [rho'] using
        prefixCountCanonicalRho_ne_zero
          (d := d) (m := m) hd2 t
          (prefixCountFirstHitSymbolMapInv hd2 t s w)
    have hi_val : i.val = s.val - 1 := rfl
    omega
  have hhit :
      prefixCountCanonicalRhoHitNat t w (rho'.val - 1) := by
    rw [hmap] at hhit'
    exact
      (prefixCountCanonicalRhoHitNat_rootStepInv_iff_of_ne
        (d := d) (m := m) (t := t) (w := w)
        (i := i) (j := rho'.val - 1) hne).1 hhit'
  have hbefore :
      (rho'.val - 1) + 1 <
        (prefixCountCanonicalRho d m hd2 t w).val := by
    have hnonzero' : rho'.val ≠ 0 := by
      simpa [rho'] using
        prefixCountCanonicalRho_ne_zero
          (d := d) (m := m) hd2 t
          (prefixCountFirstHitSymbolMapInv hd2 t s w)
    omega
  exact
    (prefixCountCanonicalRho_no_hit_before
      (d := d) (m := m) hd2 (t := t) (w := w) hbefore)
      hhit

theorem prefixCountFirstHitSymbolMapInv_apply_symbolMap_of_not_rho_lt
    {d m : Nat} (hd2 : 2 ≤ d)
    (t : ZMod m) {s : Fin d} (w : PrefixCountRootState d m)
    (hs0 : s.val ≠ 0) (hs1 : s.val ≠ 1)
    (hnot : ¬(prefixCountCanonicalRho d m hd2 t w).val < s.val) :
    prefixCountFirstHitSymbolMapInv hd2 t s
        (prefixCountFirstHitSymbolMap hd2 t s w) = w := by
  let i : Fin d := ⟨s.val - 1, by omega⟩
  have hmap :
      prefixCountFirstHitSymbolMap hd2 t s w =
        prefixCountRootStep d m i w := by
    unfold prefixCountFirstHitSymbolMap
    rw [prefixCountLambdaRho_eq_pred
      (prefixCountCanonicalRho d m hd2 t w) hs0 hs1 hnot]
  have hnot' :
      ¬ (prefixCountCanonicalRho d m hd2 t
          (prefixCountRootStep d m i w)).val < s.val := by
    have h0 :=
      prefixCountFirstHitSymbolMap_not_rho_lt_of_not_rho_lt
        hd2 t w hs0 hs1 hnot
    simpa [hmap] using h0
  unfold prefixCountFirstHitSymbolMapInv prefixCountFirstHitSymbolMap
  rw [prefixCountLambdaRho_eq_pred
    (prefixCountCanonicalRho d m hd2 t w) hs0 hs1 hnot]
  change
    prefixCountRootStepInv d m
        (prefixCountLambdaRho d
          (prefixCountCanonicalRho d m hd2 t
            (prefixCountRootStep d m i w)) s)
        (prefixCountRootStep d m i w) = w
  rw [prefixCountLambdaRho_eq_pred
    (prefixCountCanonicalRho d m hd2 t
      (prefixCountRootStep d m i w)) hs0 hs1 hnot']
  exact prefixCountRootStepInv_apply_step i w

theorem prefixCountFirstHitSymbolMap_apply_inv_of_not_rho_lt
    {d m : Nat} (hd2 : 2 ≤ d)
    (t : ZMod m) {s : Fin d} (w : PrefixCountRootState d m)
    (hs0 : s.val ≠ 0) (hs1 : s.val ≠ 1)
    (hnot : ¬(prefixCountCanonicalRho d m hd2 t w).val < s.val) :
    prefixCountFirstHitSymbolMap hd2 t s
        (prefixCountFirstHitSymbolMapInv hd2 t s w) = w := by
  let i : Fin d := ⟨s.val - 1, by omega⟩
  have hmap :
      prefixCountFirstHitSymbolMapInv hd2 t s w =
        prefixCountRootStepInv d m i w := by
    unfold prefixCountFirstHitSymbolMapInv
    rw [prefixCountLambdaRho_eq_pred
      (prefixCountCanonicalRho d m hd2 t w) hs0 hs1 hnot]
  have hnot' :
      ¬ (prefixCountCanonicalRho d m hd2 t
          (prefixCountRootStepInv d m i w)).val < s.val := by
    have h0 :=
      prefixCountFirstHitSymbolMapInv_not_rho_lt_of_not_rho_lt
        hd2 t w hs0 hs1 hnot
    simpa [hmap] using h0
  unfold prefixCountFirstHitSymbolMapInv prefixCountFirstHitSymbolMap
  rw [prefixCountLambdaRho_eq_pred
    (prefixCountCanonicalRho d m hd2 t w) hs0 hs1 hnot]
  change
    prefixCountRootStep d m
        (prefixCountLambdaRho d
          (prefixCountCanonicalRho d m hd2 t
            (prefixCountRootStepInv d m i w)) s)
        (prefixCountRootStepInv d m i w) = w
  rw [prefixCountLambdaRho_eq_pred
    (prefixCountCanonicalRho d m hd2 t
      (prefixCountRootStepInv d m i w)) hs0 hs1 hnot']
  exact prefixCountRootStep_apply_inv i w

theorem prefixCountFirstHitCanonicalSchedule_layerMap_eq_symbolMap
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {M : Matrix (Fin d) (Fin d) Nat}
    (L : PrefixCount.LayerPermCounts d m M)
    (t : ZMod m) (c : Fin d) :
    (prefixCountFirstHitCanonicalSchedule hd2 L).layerMap t c =
      prefixCountFirstHitSymbolMap hd2 t
        (L.layer (prefixCountLayerIndex t) c) := rfl

theorem prefixCountFirstHitCanonicalSchedule_prefixMap_apply_zero
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {M : Matrix (Fin d) (Fin d) Nat}
    (L : PrefixCount.LayerPermCounts d m M) (c : Fin d) :
    ∀ k : Nat, ∀ w : PrefixCountRootState d m,
      ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c k w)
          ⟨0, by omega⟩ =
        w ⟨0, by omega⟩ +
          ∑ t ∈ Finset.range k,
            if (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c).val = 0
            then (1 : ZMod m) else 0
  | 0, w => by
      simp [Shared.RootFlatSchedule.prefixMap]
  | k + 1, w => by
      rw [Shared.RootFlatSchedule.prefixMap]
      rw [prefixCountFirstHitCanonicalSchedule_layerMap_eq_symbolMap]
      change
        prefixCountFirstHitSymbolMap hd2 ((k : Nat) : ZMod m)
          (L.layer (prefixCountLayerIndex ((k : Nat) : ZMod m)) c)
          ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c k w)
          ⟨0, by omega⟩ = _
      rw [prefixCountFirstHitSymbolMap_apply_zero]
      rw [prefixCountFirstHitCanonicalSchedule_prefixMap_apply_zero
        hd2 L c k w]
      rw [Finset.sum_range_succ]
      by_cases hzero :
          (L.layer (prefixCountLayerIndex ((k : Nat) : ZMod m)) c).val = 0
      · simp [hzero]
        ring
      · simp [hzero]

theorem prefixCountFirstHitCanonicalSchedule_prefixMap_apply_coord
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {M : Matrix (Fin d) (Fin d) Nat}
    (L : PrefixCount.LayerPermCounts d m M) (c : Fin d) :
    ∀ k : Nat, ∀ w : PrefixCountRootState d m, ∀ j : Fin (d - 1),
      ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c k w) j =
        w j +
          ∑ t ∈ Finset.range k,
            if (prefixCountLambdaRho d
                (prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m)
                  ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t w))
                (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c)).val
                = j.val
            then (1 : ZMod m) else 0
  | 0, w, j => by
      simp [Shared.RootFlatSchedule.prefixMap]
  | k + 1, w, j => by
      rw [Shared.RootFlatSchedule.prefixMap]
      rw [prefixCountFirstHitCanonicalSchedule_layerMap_eq_symbolMap]
      change
        prefixCountFirstHitSymbolMap hd2 ((k : Nat) : ZMod m)
          (L.layer (prefixCountLayerIndex ((k : Nat) : ZMod m)) c)
          ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c k w)
          j = _
      rw [prefixCountFirstHitSymbolMap_apply_coord]
      rw [prefixCountFirstHitCanonicalSchedule_prefixMap_apply_coord
        hd2 L c k w j]
      rw [Finset.sum_range_succ]
      by_cases hhit :
          (prefixCountLambdaRho d
              (prefixCountCanonicalRho d m hd2 ((k : Nat) : ZMod m)
                ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c k w))
              (L.layer (prefixCountLayerIndex ((k : Nat) : ZMod m)) c)).val
            = j.val
      · simp [hhit]
        ring
      · simp [hhit]

theorem prefixCountFirstHitCanonicalSchedule_returnMap_apply_zero
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {M : Matrix (Fin d) (Fin d) Nat}
    (L : PrefixCount.LayerPermCounts d m M) (c : Fin d)
    (w : PrefixCountRootState d m) :
    ((prefixCountFirstHitCanonicalSchedule hd2 L).returnMap c w)
        ⟨0, by omega⟩ =
      w ⟨0, by omega⟩ +
        (M c (PrefixCount.Parts.colZero hd2) : ZMod m) := by
  rw [Shared.RootFlatSchedule.returnMap_eq_prefixMap]
  rw [prefixCountFirstHitCanonicalSchedule_prefixMap_apply_zero]
  congr 1
  let fNat : Nat → Nat := fun t =>
    if (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c).val = 0
    then 1 else 0
  have hRangeNat :
      (∑ t ∈ Finset.range m, fNat t) =
        M c (PrefixCount.Parts.colZero hd2) := by
    calc
      (∑ t ∈ Finset.range m, fNat t)
          = ∑ t : Fin m, fNat t.val := by
              rw [Fin.sum_univ_eq_sum_range fNat m]
      _ = ∑ t : Fin m,
            if L.layer t c = PrefixCount.Parts.colZero hd2
            then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro t _ht
              have hidx := prefixCountLayerIndex_natCast_val t
              by_cases hzero : (L.layer t c).val = 0
              · have hcol :
                    L.layer t c = PrefixCount.Parts.colZero hd2 := by
                  ext
                  simpa [PrefixCount.Parts.colZero] using hzero
                simp [fNat, hidx, hzero, hcol, PrefixCount.Parts.colZero]
              · have hcol :
                    L.layer t c ≠ (⟨0, by omega⟩ : Fin d) := by
                  intro h
                  apply hzero
                  exact congrArg Fin.val h
                simp [fNat, hidx, hcol, PrefixCount.Parts.colZero]
                exact hzero
      _ = M c (PrefixCount.Parts.colZero hd2) :=
          L.count_eq c (PrefixCount.Parts.colZero hd2)
  have hCast :
      ((∑ t ∈ Finset.range m, fNat t : Nat) : ZMod m) =
        ∑ t ∈ Finset.range m,
          if (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c).val = 0
          then (1 : ZMod m) else 0 := by
    simp [fNat]
  rw [← hCast, hRangeNat]

theorem prefixCountFirstHitCanonicalSchedule_returnMap_apply_coord
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {M : Matrix (Fin d) (Fin d) Nat}
    (L : PrefixCount.LayerPermCounts d m M) (c : Fin d)
    (w : PrefixCountRootState d m) (j : Fin (d - 1)) :
    ((prefixCountFirstHitCanonicalSchedule hd2 L).returnMap c w) j =
      w j +
        ∑ t ∈ Finset.range m,
          if (prefixCountLambdaRho d
              (prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m)
                ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t w))
              (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c)).val
              = j.val
          then (1 : ZMod m) else 0 := by
  rw [Shared.RootFlatSchedule.returnMap_eq_prefixMap]
  exact prefixCountFirstHitCanonicalSchedule_prefixMap_apply_coord
    hd2 L c m w j

theorem prefixCountFirstHitCanonicalSchedule_returnMap_apply_zero_parts
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    (w : PrefixCountRootState d m) :
    ((prefixCountFirstHitCanonicalSchedule hd2 L).returnMap c w)
        ⟨0, by omega⟩ =
      w ⟨0, by omega⟩ + (C.zero c : ZMod m) := by
  simpa using
    prefixCountFirstHitCanonicalSchedule_returnMap_apply_zero
      (hd2 := hd2) (L := L) c w

theorem prefixCountFirstHitCanonicalSchedule_zeroCoordinateCycle
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d} (hC : C.Admissible m)
    (c : Fin d) :
    Shared.IsSingleCycleMap
      (fun z : ZMod m => z + (C.zero c : ZMod m)) :=
  Shared.zmod_add_single_cycle_of_coprime (hC.prim_zero c)

def prefixCountFirstHitReturnBaseStep {d m : Nat}
    (C : PrefixCount.Parts d) (c : Fin d) : ZMod m → ZMod m :=
  fun z => z + (C.zero c : ZMod m)

noncomputable def prefixCountFirstHitReturnBaseStep_cycleCoordinate
    {d m : Nat} [NeZero m]
    {C : PrefixCount.Parts d} (hC : C.Admissible m) (c : Fin d) :
    Shared.CycleCoordinate m
      (prefixCountFirstHitReturnBaseStep (m := m) C c) := by
  unfold prefixCountFirstHitReturnBaseStep
  exact Shared.CycleCoordinate.zmodAddConstOfCoprime (hC.prim_zero c)

theorem prefixCountFirstHitReturnBaseStep_iterate
    {d m : Nat} (C : PrefixCount.Parts d) (c : Fin d) :
    ∀ n : Nat, ∀ z : ZMod m,
      ((prefixCountFirstHitReturnBaseStep (m := m) C c)^[n]) z =
        z + (n : ZMod m) * (C.zero c : ZMod m)
  | 0, z => by simp
  | n + 1, z => by
      rw [Function.iterate_succ_apply']
      rw [prefixCountFirstHitReturnBaseStep_iterate C c n]
      simp [prefixCountFirstHitReturnBaseStep, Nat.cast_add]
      ring

theorem prefixCountFirstHitReturnBaseStep_iterate_modulus
    {d m : Nat} [NeZero m] (C : PrefixCount.Parts d) (c : Fin d)
    (z : ZMod m) :
    ((prefixCountFirstHitReturnBaseStep (m := m) C c)^[m]) z = z := by
  rw [prefixCountFirstHitReturnBaseStep_iterate]
  simp

theorem prefixCountFirstHitReturnBaseStep_cover
    {d m : Nat} [NeZero m] {C : PrefixCount.Parts d}
    (hC : C.Admissible m) (c : Fin d) (base z : ZMod m) :
    ∃ k : Nat, k < m ∧
      ((prefixCountFirstHitReturnBaseStep (m := m) C c)^[k]) base = z := by
  let u : (ZMod m)ˣ := ZMod.unitOfCoprime (C.zero c) (hC.prim_zero c)
  let target : ZMod m := (u⁻¹ : ZMod m) * (z - base)
  refine ⟨target.val, ZMod.val_lt target, ?_⟩
  rw [prefixCountFirstHitReturnBaseStep_iterate]
  have htarget : (target.val : ZMod m) = target :=
    ZMod.natCast_zmod_val target
  have hu : (u : ZMod m) = (C.zero c : ZMod m) :=
    ZMod.coe_unitOfCoprime (C.zero c) (hC.prim_zero c)
  calc
    base + (target.val : ZMod m) * (C.zero c : ZMod m)
        = base + target * (u : ZMod m) := by rw [htarget, hu]
    _ = z := by
        have huinv : (u⁻¹ : ZMod m) * (u : ZMod m) = 1 := by simp
        change base + ((u⁻¹ : ZMod m) * (z - base)) * (u : ZMod m) = z
        calc
          base + ((u⁻¹ : ZMod m) * (z - base)) * (u : ZMod m)
              = base + ((u⁻¹ : ZMod m) * (u : ZMod m)) * (z - base) := by
                  ring
          _ = z := by
              rw [huinv]
              ring

noncomputable def prefixCountFirstHitReturnFiberStep
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d) :
    ZMod m → (Fin (d - 2) → ZMod m) → (Fin (d - 2) → ZMod m) :=
  fun z tail =>
    (prefixCountRootStateHeadTailEquiv d m hd2
      ((prefixCountFirstHitCanonicalSchedule hd2 L).returnMap c
        ((prefixCountRootStateHeadTailEquiv d m hd2).symm (z, tail)))).2

theorem prefixCountFirstHitReturnFiberStep_apply
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    (z : ZMod m) (tail : Fin (d - 2) → ZMod m) (j : Fin (d - 2)) :
    prefixCountFirstHitReturnFiberStep hd2 L c z tail j =
      tail j +
        ∑ t ∈ Finset.range m,
          if (prefixCountLambdaRho d
              (prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m)
                ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t
                  ((prefixCountRootStateHeadTailEquiv d m hd2).symm
                    (z, tail))))
              (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c)).val
              = j.val + 1
          then (1 : ZMod m) else 0 := by
  unfold prefixCountFirstHitReturnFiberStep
  rw [prefixCountRootStateHeadTailEquiv_snd]
  rw [prefixCountFirstHitCanonicalSchedule_returnMap_apply_coord
    (hd2 := hd2) (L := L) c
    ((prefixCountRootStateHeadTailEquiv d m hd2).symm (z, tail))
    ⟨j.val + 1, by omega⟩]
  simp

theorem prefixCountFirstHitReturnFiberStep_apply_cases
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    (z : ZMod m) (tail : Fin (d - 2) → ZMod m) (j : Fin (d - 2)) :
    prefixCountFirstHitReturnFiberStep hd2 L c z tail j =
      tail j +
        ∑ t ∈ Finset.range m,
          if
            let rho :=
              prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m)
                ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t
                  ((prefixCountRootStateHeadTailEquiv d m hd2).symm
                    (z, tail)))
            let s := L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c
            (s.val = 1 ∧ rho.val = j.val + 1) ∨
              (s.val = j.val + 1 ∧ 1 < s.val ∧ rho.val < s.val) ∨
              (s.val = j.val + 2 ∧ ¬ rho.val < s.val)
          then (1 : ZMod m) else 0 := by
  rw [prefixCountFirstHitReturnFiberStep_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro t _ht
  let rho :=
    prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m)
      ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t
        ((prefixCountRootStateHeadTailEquiv d m hd2).symm
          (z, tail)))
  let s := L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c
  have hiff :
      (prefixCountLambdaRho d rho s).val = j.val + 1 ↔
        (s.val = 1 ∧ rho.val = j.val + 1) ∨
          (s.val = j.val + 1 ∧ 1 < s.val ∧ rho.val < s.val) ∨
          (s.val = j.val + 2 ∧ ¬ rho.val < s.val) := by
    simpa [Nat.add_assoc] using
      (prefixCountLambdaRho_val_eq_pos_iff
        (d := d) rho s (l := j.val + 1) (Nat.succ_pos j.val))
  by_cases h :
      (prefixCountLambdaRho d rho s).val = j.val + 1
  · have hcase := hiff.mp h
    simp [rho, s, h, hcase]
  · have hcase :
      ¬ ((s.val = 1 ∧ rho.val = j.val + 1) ∨
          (s.val = j.val + 1 ∧ 1 < s.val ∧ rho.val < s.val) ∨
          (s.val = j.val + 2 ∧ ¬ rho.val < s.val)) := by
        intro hcase
        exact h (hiff.mpr hcase)
    simp [rho, s, h, hcase]

theorem prefixCountFirstHitCanonicalSchedule_returnMap_headTail_conj
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    (x : ZMod m × (Fin (d - 2) → ZMod m)) :
    prefixCountRootStateHeadTailEquiv d m hd2
        ((prefixCountFirstHitCanonicalSchedule hd2 L).returnMap c
          ((prefixCountRootStateHeadTailEquiv d m hd2).symm x))
      =
    Shared.skewProductMap
      (prefixCountFirstHitReturnBaseStep C c)
      (prefixCountFirstHitReturnFiberStep hd2 L c) x := by
  rcases x with ⟨z, tail⟩
  ext j
  · simp [Shared.skewProductMap, prefixCountFirstHitReturnBaseStep,
      prefixCountFirstHitReturnFiberStep,
      prefixCountFirstHitCanonicalSchedule_returnMap_apply_zero_parts]
  · rfl

theorem prefixCountFirstHitReturnSkew_iterate_conj
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d) :
    ∀ n : Nat, ∀ x : ZMod m × (Fin (d - 2) → ZMod m),
      (Shared.skewProductMap
        (prefixCountFirstHitReturnBaseStep (m := m) C c)
        (prefixCountFirstHitReturnFiberStep hd2 L c))^[n] x =
      prefixCountRootStateHeadTailEquiv d m hd2
        (((prefixCountFirstHitCanonicalSchedule hd2 L).returnMap c)^[n]
          ((prefixCountRootStateHeadTailEquiv d m hd2).symm x))
  | 0, x => by simp
  | n + 1, x => by
      rw [Function.iterate_succ_apply']
      rw [prefixCountFirstHitReturnSkew_iterate_conj hd2 L c n x]
      rw [← prefixCountFirstHitCanonicalSchedule_returnMap_headTail_conj
        (hd2 := hd2) L c
        (prefixCountRootStateHeadTailEquiv d m hd2
          (((prefixCountFirstHitCanonicalSchedule hd2 L).returnMap c)^[n]
            ((prefixCountRootStateHeadTailEquiv d m hd2).symm x)))]
      simp
      exact
        (Function.Commute.refl
          ((prefixCountFirstHitCanonicalSchedule hd2 L).returnMap c)).iterate_right n
          ((prefixCountRootStateHeadTailEquiv d m hd2).symm x)

theorem prefixCountFirstHitSectionReturn_eq_tail_of_returnMap_iterate
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    (tail : Fin (d - 2) → ZMod m) :
    Shared.sectionReturn
        (Shared.skewProductMap
          (prefixCountFirstHitReturnBaseStep (m := m) C c)
          (prefixCountFirstHitReturnFiberStep hd2 L c))
        (0 : ZMod m) m tail =
      (prefixCountRootStateHeadTailEquiv d m hd2
        (((prefixCountFirstHitCanonicalSchedule hd2 L).returnMap c)^[m]
          ((prefixCountRootStateHeadTailEquiv d m hd2).symm
            ((0 : ZMod m), tail)))).2 := by
  unfold Shared.sectionReturn
  rw [prefixCountFirstHitReturnSkew_iterate_conj]

noncomputable def prefixCountFirstHitReturnTailMonodromy
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d) :
    (Fin (d - 2) → ZMod m) → (Fin (d - 2) → ZMod m) :=
  fun tail =>
    (prefixCountRootStateHeadTailEquiv d m hd2
      (((prefixCountFirstHitCanonicalSchedule hd2 L).returnMap c)^[m]
        ((prefixCountRootStateHeadTailEquiv d m hd2).symm
          ((0 : ZMod m), tail)))).2

theorem prefixCountFirstHitSectionReturn_eq_returnTailMonodromy
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d) :
    Shared.sectionReturn
        (Shared.skewProductMap
          (prefixCountFirstHitReturnBaseStep (m := m) C c)
          (prefixCountFirstHitReturnFiberStep hd2 L c))
        (0 : ZMod m) m =
      prefixCountFirstHitReturnTailMonodromy hd2 L c := by
  funext tail
  exact prefixCountFirstHitSectionReturn_eq_tail_of_returnMap_iterate
    hd2 L c tail

theorem prefixCountFirstHitReturnTailMonodromy_eq_fiberIterate
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d) :
    prefixCountFirstHitReturnTailMonodromy hd2 L c =
      Shared.skewFiberIterate
        (prefixCountFirstHitReturnBaseStep (m := m) C c)
        (prefixCountFirstHitReturnFiberStep hd2 L c)
        m (0 : ZMod m) := by
  rw [← prefixCountFirstHitSectionReturn_eq_returnTailMonodromy
    (hd2 := hd2) (C := C) L c]
  rw [Shared.sectionReturn_skewProductMap_eq_fiberIterate]

theorem prefixCountFirstHitReturnTailMonodromy_apply_eq_fiberIterate
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    (tail : Fin (d - 2) → ZMod m) :
    prefixCountFirstHitReturnTailMonodromy hd2 L c tail =
      Shared.skewFiberIterate
        (prefixCountFirstHitReturnBaseStep (m := m) C c)
        (prefixCountFirstHitReturnFiberStep hd2 L c)
        m (0 : ZMod m) tail := by
  rw [prefixCountFirstHitReturnTailMonodromy_eq_fiberIterate]

theorem prefixCountFirstHitCanonicalSchedule_returnMap_singleCycle_of_headTailMonodromy
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d} (hC : C.Admissible m)
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    (base : ZMod m) (period : Nat)
    (hfiber :
      ∀ z : ZMod m,
        Function.Bijective (prefixCountFirstHitReturnFiberStep hd2 L c z))
    (hreturnBase :
      ((prefixCountFirstHitReturnBaseStep (m := m) C c)^[period]) base = base)
    (hbaseCover :
      ∀ z : ZMod m, ∃ k : Nat,
        k < period ∧
          ((prefixCountFirstHitReturnBaseStep (m := m) C c)^[k]) base = z)
    (hmonodromy :
      Shared.IsSingleCycleMap
        (Shared.sectionReturn
          (Shared.skewProductMap
            (prefixCountFirstHitReturnBaseStep (m := m) C c)
            (prefixCountFirstHitReturnFiberStep hd2 L c))
          base period)) :
    Shared.IsSingleCycleMap
      ((prefixCountFirstHitCanonicalSchedule hd2 L).returnMap c) := by
  have hbase :
      Function.Bijective
        (prefixCountFirstHitReturnBaseStep (m := m) C c) := by
    have hcycle :=
      prefixCountFirstHitCanonicalSchedule_zeroCoordinateCycle
        (hd2 := hd2) (hC := hC) c
    simpa [prefixCountFirstHitReturnBaseStep] using hcycle.1
  have hskew :
      Shared.IsSingleCycleMap
          (Shared.skewProductMap
          (prefixCountFirstHitReturnBaseStep (m := m) C c)
          (prefixCountFirstHitReturnFiberStep hd2 L c)) :=
    Shared.single_cycle_of_skewProduct_base_orbit_monodromy
      (prefixCountFirstHitReturnBaseStep (m := m) C c)
      (prefixCountFirstHitReturnFiberStep hd2 L c)
      base period hbase hfiber hreturnBase hbaseCover hmonodromy
  exact
    Shared.single_cycle_of_equiv_conj
      (prefixCountRootStateHeadTailEquiv d m hd2).symm
      ((prefixCountFirstHitCanonicalSchedule hd2 L).returnMap c)
      (Shared.skewProductMap
        (prefixCountFirstHitReturnBaseStep (m := m) C c)
        (prefixCountFirstHitReturnFiberStep hd2 L c))
      hskew
      (prefixCountFirstHitCanonicalSchedule_returnMap_headTail_conj
        hd2 L c)

theorem prefixCountFirstHitCanonicalSchedule_returnMap_singleCycle_of_unitBaseHeadTailMonodromy
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d} (hC : C.Admissible m)
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    (hfiber :
      ∀ z : ZMod m,
        Function.Bijective (prefixCountFirstHitReturnFiberStep hd2 L c z))
    (hmonodromy :
      Shared.IsSingleCycleMap
        (Shared.sectionReturn
          (Shared.skewProductMap
            (prefixCountFirstHitReturnBaseStep (m := m) C c)
            (prefixCountFirstHitReturnFiberStep hd2 L c))
          (0 : ZMod m) m)) :
    Shared.IsSingleCycleMap
      ((prefixCountFirstHitCanonicalSchedule hd2 L).returnMap c) :=
  prefixCountFirstHitCanonicalSchedule_returnMap_singleCycle_of_headTailMonodromy
    (hd2 := hd2) hC L c (0 : ZMod m) m
    hfiber
    (prefixCountFirstHitReturnBaseStep_iterate_modulus C c (0 : ZMod m))
    (prefixCountFirstHitReturnBaseStep_cover hC c (0 : ZMod m))
    hmonodromy

def PrefixCountFirstHitSymbolMapsBijectiveGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d),
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    ∀ t : ZMod m, ∀ s : Fin d,
      Function.Bijective (prefixCountFirstHitSymbolMap hd2 t s)

def PrefixCountFirstHitSymbolMapInverseLawGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d),
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    ∀ t : ZMod m, ∀ s : Fin d,
      Function.LeftInverse
        (prefixCountFirstHitSymbolMapInv hd2 t s)
        (prefixCountFirstHitSymbolMap hd2 t s) ∧
      Function.RightInverse
        (prefixCountFirstHitSymbolMapInv hd2 t s)
        (prefixCountFirstHitSymbolMap hd2 t s)

def PrefixCountFirstHitTailSymbolMapInverseLawGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d),
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    ∀ t : ZMod m, ∀ s : Fin d,
      s.val ≠ 0 → s.val ≠ 1 →
      Function.LeftInverse
        (prefixCountFirstHitSymbolMapInv hd2 t s)
        (prefixCountFirstHitSymbolMap hd2 t s) ∧
      Function.RightInverse
        (prefixCountFirstHitSymbolMapInv hd2 t s)
        (prefixCountFirstHitSymbolMap hd2 t s)

theorem prefixCountFirstHitTailSymbolMapInverseLawGoal :
    PrefixCountFirstHitTailSymbolMapInverseLawGoal := by
  intro d m _inst hd2 _hdodd _hd5 _hmodd _hdm t s hs0 hs1
  constructor
  · intro w
    by_cases hlt :
        (prefixCountCanonicalRho d m hd2 t w).val < s.val
    · exact prefixCountFirstHitSymbolMapInv_apply_symbolMap_of_rho_lt
        hd2 t w hs0 hs1 hlt
    · exact prefixCountFirstHitSymbolMapInv_apply_symbolMap_of_not_rho_lt
        hd2 t w hs0 hs1 hlt
  · intro w
    by_cases hlt :
        (prefixCountCanonicalRho d m hd2 t w).val < s.val
    · exact prefixCountFirstHitSymbolMap_apply_inv_of_rho_lt
        hd2 t w hs0 hs1 hlt
    · exact prefixCountFirstHitSymbolMap_apply_inv_of_not_rho_lt
        hd2 t w hs0 hs1 hlt

theorem prefixCountFirstHitSymbolMapInverseLawGoal_of_tail
    (hTail : PrefixCountFirstHitTailSymbolMapInverseLawGoal) :
    PrefixCountFirstHitSymbolMapInverseLawGoal := by
  intro d m _inst hd2 hdodd hd5 hmodd hdm t s
  by_cases hs0 : s.val = 0
  · exact prefixCountFirstHitSymbolMap_inverseLaw_of_val_zero hd2 t hs0
  · by_cases hs1 : s.val = 1
    · exact prefixCountFirstHitSymbolMap_inverseLaw_of_val_one hd2 t hs1
    · exact hTail hd2 hdodd hd5 hmodd hdm t s hs0 hs1

theorem prefixCountFirstHitSymbolMapInverseLawGoal :
    PrefixCountFirstHitSymbolMapInverseLawGoal :=
  prefixCountFirstHitSymbolMapInverseLawGoal_of_tail
    prefixCountFirstHitTailSymbolMapInverseLawGoal

theorem prefixCountFirstHitSymbolMapsBijectiveGoal_of_inverseLaw
    (hInv : PrefixCountFirstHitSymbolMapInverseLawGoal) :
    PrefixCountFirstHitSymbolMapsBijectiveGoal := by
  intro d m _inst hd2 hdodd hd5 hmodd hdm t s
  rcases hInv hd2 hdodd hd5 hmodd hdm t s with ⟨hLeft, hRight⟩
  constructor
  · intro x y hxy
    have h := congrArg (prefixCountFirstHitSymbolMapInv hd2 t s) hxy
    calc
      x = prefixCountFirstHitSymbolMapInv hd2 t s
            (prefixCountFirstHitSymbolMap hd2 t s x) := (hLeft x).symm
      _ = prefixCountFirstHitSymbolMapInv hd2 t s
            (prefixCountFirstHitSymbolMap hd2 t s y) := h
      _ = y := hLeft y
  · intro y
    exact ⟨prefixCountFirstHitSymbolMapInv hd2 t s y, hRight y⟩

theorem prefixCountFirstHitSymbolMapsBijectiveGoal :
    PrefixCountFirstHitSymbolMapsBijectiveGoal :=
  prefixCountFirstHitSymbolMapsBijectiveGoal_of_inverseLaw
    prefixCountFirstHitSymbolMapInverseLawGoal

def PrefixCountFirstHitCanonicalLayerBijectiveGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) →
    (prefixCountFirstHitCanonicalSchedule hd2 L).layerBijective

def PrefixCountFirstHitCanonicalReturnsSingleCycleGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) →
    (prefixCountFirstHitCanonicalSchedule hd2 L).returnsSingleCycle

def PrefixCountFirstHitHeadTailMonodromyGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) →
    ∀ c : Fin d,
      (∀ z : ZMod m,
        Function.Bijective (prefixCountFirstHitReturnFiberStep hd2 L c z)) ∧
      Shared.IsSingleCycleMap
        (Shared.sectionReturn
          (Shared.skewProductMap
            (prefixCountFirstHitReturnBaseStep (m := m) C c)
            (prefixCountFirstHitReturnFiberStep hd2 L c))
          (0 : ZMod m) m)

def PrefixCountFirstHitHeadTailSectionMonodromyGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) →
    ∀ c : Fin d,
      Shared.IsSingleCycleMap
        (Shared.sectionReturn
          (Shared.skewProductMap
            (prefixCountFirstHitReturnBaseStep (m := m) C c)
            (prefixCountFirstHitReturnFiberStep hd2 L c))
          (0 : ZMod m) m)

def PrefixCountFirstHitReturnTailMonodromyGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) →
    ∀ c : Fin d,
      Shared.IsSingleCycleMap
        (prefixCountFirstHitReturnTailMonodromy hd2 L c)

def PrefixCountFirstHitReturnTailMonodromyOrbitGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) →
    ∀ c : Fin d, ∀ tail₁ tail₂ : Fin (d - 2) → ZMod m,
      ∃ n : Nat,
        (prefixCountFirstHitReturnTailMonodromy hd2 L c)^[n] tail₁ =
          tail₂

def PrefixCountFirstHitReturnTailRankGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) →
    ∀ c : Fin d,
      ∃ rank :
          ((Fin (d - 2) → ZMod m) → ZMod (m ^ (d - 2))),
        Function.Bijective rank ∧
        ∀ tail : Fin (d - 2) → ZMod m,
          rank (prefixCountFirstHitReturnTailMonodromy hd2 L c tail) =
            rank tail + 1

def PrefixCountFirstHitReturnTailRankEquivGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) →
    ∀ c : Fin d,
      ∃ e :
          ((Fin (d - 2) → ZMod m) ≃ ZMod (m ^ (d - 2))),
        ∀ tail : Fin (d - 2) → ZMod m,
          e (prefixCountFirstHitReturnTailMonodromy hd2 L c tail) =
            e tail + 1

def PrefixCountFirstHitReturnTailCycleCoordinateGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) →
    ∀ c : Fin d,
      Shared.CycleCoordinate (m ^ (d - 2))
        (prefixCountFirstHitReturnTailMonodromy hd2 L c)

theorem prefixCountFirstHitHeadTailSectionMonodromyGoal_of_returnTailMonodromy
    (hTail : PrefixCountFirstHitReturnTailMonodromyGoal) :
    PrefixCountFirstHitHeadTailSectionMonodromyGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L c
  rw [prefixCountFirstHitSectionReturn_eq_returnTailMonodromy
    (hd2 := hd2) (C := C) L c]
  exact hTail hd2 hdodd hd5 hmodd hdm hC L c

theorem prefixCountFirstHitCanonicalReturnsSingleCycleGoal_of_headTailMonodromy
    (hMono : PrefixCountFirstHitHeadTailMonodromyGoal) :
    PrefixCountFirstHitCanonicalReturnsSingleCycleGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L c
  rcases hMono hd2 hdodd hd5 hmodd hdm hC L c with
    ⟨hfiber, hmonodromy⟩
  exact
    prefixCountFirstHitCanonicalSchedule_returnMap_singleCycle_of_unitBaseHeadTailMonodromy
      hd2 hC L c hfiber hmonodromy

def PrefixCountFirstHitCanonicalScheduleAuxGoal : Prop :=
  PrefixCountFirstHitCanonicalLayerBijectiveGoal ∧
  PrefixCountFirstHitCanonicalReturnsSingleCycleGoal

theorem prefixCountFirstHitCanonicalLayerBijectiveGoal_of_symbolMaps
    (hSym : PrefixCountFirstHitSymbolMapsBijectiveGoal) :
    PrefixCountFirstHitCanonicalLayerBijectiveGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm _hC L t c
  rw [prefixCountFirstHitCanonicalSchedule_layerMap_eq_symbolMap]
  exact hSym hd2 hdodd hd5 hmodd hdm t (L.layer (prefixCountLayerIndex t) c)

theorem prefixCountFirstHitCanonicalLayerBijectiveGoal :
    PrefixCountFirstHitCanonicalLayerBijectiveGoal :=
  prefixCountFirstHitCanonicalLayerBijectiveGoal_of_symbolMaps
    prefixCountFirstHitSymbolMapsBijectiveGoal

theorem prefixCountFirstHitReturnFiberStep_bijective
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (hdodd : Odd d) (hd5 : 5 ≤ d) (hmodd : Odd m) (hdm : d ≤ m)
    (hC : C.Admissible m)
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d) :
    ∀ z : ZMod m,
      Function.Bijective (prefixCountFirstHitReturnFiberStep hd2 L c z) := by
  have hLayer :
      (prefixCountFirstHitCanonicalSchedule hd2 L).layerBijective :=
    prefixCountFirstHitCanonicalLayerBijectiveGoal
      hd2 hdodd hd5 hmodd hdm hC L
  have hReturn :
      Function.Bijective
        ((prefixCountFirstHitCanonicalSchedule hd2 L).returnMap c) := by
    rw [Shared.RootFlatSchedule.returnMap_eq_prefixMap]
    exact Shared.RootFlatSchedule.prefixMap_bijective
      (prefixCountFirstHitCanonicalSchedule hd2 L) hLayer c m
  have hbase :
      Function.Bijective
        (prefixCountFirstHitReturnBaseStep (m := m) C c) := by
    have hcycle :=
      prefixCountFirstHitCanonicalSchedule_zeroCoordinateCycle
        (hd2 := hd2) (hC := hC) c
    simpa [prefixCountFirstHitReturnBaseStep] using hcycle.1
  have hSkew :
      Function.Bijective
        (Shared.skewProductMap
          (prefixCountFirstHitReturnBaseStep (m := m) C c)
          (prefixCountFirstHitReturnFiberStep hd2 L c)) := by
    refine Shared.bijective_of_equiv_conj
      (prefixCountRootStateHeadTailEquiv d m hd2)
      (Shared.skewProductMap
        (prefixCountFirstHitReturnBaseStep (m := m) C c)
        (prefixCountFirstHitReturnFiberStep hd2 L c))
      ((prefixCountFirstHitCanonicalSchedule hd2 L).returnMap c)
      hReturn ?_
    intro w
    apply (prefixCountRootStateHeadTailEquiv d m hd2).injective
    calc
      prefixCountRootStateHeadTailEquiv d m hd2
          ((prefixCountRootStateHeadTailEquiv d m hd2).symm
            (Shared.skewProductMap
              (prefixCountFirstHitReturnBaseStep (m := m) C c)
              (prefixCountFirstHitReturnFiberStep hd2 L c)
              (prefixCountRootStateHeadTailEquiv d m hd2 w)))
          =
          Shared.skewProductMap
            (prefixCountFirstHitReturnBaseStep (m := m) C c)
            (prefixCountFirstHitReturnFiberStep hd2 L c)
            (prefixCountRootStateHeadTailEquiv d m hd2 w) := by simp
      _ =
          prefixCountRootStateHeadTailEquiv d m hd2
            ((prefixCountFirstHitCanonicalSchedule hd2 L).returnMap c w) := by
            rw [← prefixCountFirstHitCanonicalSchedule_returnMap_headTail_conj
              (hd2 := hd2) L c (prefixCountRootStateHeadTailEquiv d m hd2 w)]
            simp
  exact
    Shared.skewProductMap_fiber_bijective_of_bijective
      (prefixCountFirstHitReturnBaseStep (m := m) C c)
      (prefixCountFirstHitReturnFiberStep hd2 L c)
      hSkew hbase

theorem prefixCountFirstHitReturnTailMonodromy_bijective
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (hdodd : Odd d) (hd5 : 5 ≤ d) (hmodd : Odd m) (hdm : d ≤ m)
    (hC : C.Admissible m)
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d) :
    Function.Bijective (prefixCountFirstHitReturnTailMonodromy hd2 L c) := by
  rw [prefixCountFirstHitReturnTailMonodromy_eq_fiberIterate
    (hd2 := hd2) (C := C) L c]
  exact
    Shared.skewFiberIterate_bijective
      (prefixCountFirstHitReturnBaseStep (m := m) C c)
      (prefixCountFirstHitReturnFiberStep hd2 L c)
      (prefixCountFirstHitReturnFiberStep_bijective
        hd2 hdodd hd5 hmodd hdm hC L c)
      m (0 : ZMod m)

theorem prefixCountFirstHitReturnTailMonodromyGoal_of_orbit
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal) :
    PrefixCountFirstHitReturnTailMonodromyGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L c
  exact ⟨
    prefixCountFirstHitReturnTailMonodromy_bijective
      hd2 hdodd hd5 hmodd hdm hC L c,
    hOrbit hd2 hdodd hd5 hmodd hdm hC L c⟩

theorem prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_rank
    (hRank : PrefixCountFirstHitReturnTailRankGoal) :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L c tail₁ tail₂
  rcases hRank hd2 hdodd hd5 hmodd hdm hC L c with
    ⟨rank, hrank, hstep⟩
  have hN : m ^ (d - 2) ≠ 0 := by
    exact pow_ne_zero (d - 2) (NeZero.ne m)
  haveI : NeZero (m ^ (d - 2)) := ⟨hN⟩
  exact
    (Shared.single_cycle_of_zmod_rank
      (prefixCountFirstHitReturnTailMonodromy hd2 L c)
      rank hrank hstep).2 tail₁ tail₂

theorem prefixCountFirstHitReturnTailRankGoal_of_rankEquiv
    (hEquiv : PrefixCountFirstHitReturnTailRankEquivGoal) :
    PrefixCountFirstHitReturnTailRankGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L c
  rcases hEquiv hd2 hdodd hd5 hmodd hdm hC L c with
    ⟨e, hstep⟩
  exact ⟨e, Equiv.bijective e, hstep⟩

theorem prefixCountFirstHitReturnTailRankEquivGoal_of_cycleCoordinate
    (hCycle : PrefixCountFirstHitReturnTailCycleCoordinateGoal) :
    PrefixCountFirstHitReturnTailRankEquivGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L c
  let K := hCycle hd2 hdodd hd5 hmodd hdm hC L c
  exact ⟨K.equiv.symm, fun tail => Shared.CycleCoordinate.rank_step K tail⟩

theorem prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_rankEquiv
    (hEquiv : PrefixCountFirstHitReturnTailRankEquivGoal) :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal :=
  prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_rank
    (prefixCountFirstHitReturnTailRankGoal_of_rankEquiv hEquiv)

theorem prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_cycleCoordinate
    (hCycle : PrefixCountFirstHitReturnTailCycleCoordinateGoal) :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal :=
  prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_rankEquiv
    (prefixCountFirstHitReturnTailRankEquivGoal_of_cycleCoordinate hCycle)

theorem prefixCountFirstHitReturnTailMonodromyGoal_of_rank
    (hRank : PrefixCountFirstHitReturnTailRankGoal) :
    PrefixCountFirstHitReturnTailMonodromyGoal :=
  prefixCountFirstHitReturnTailMonodromyGoal_of_orbit
    (prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_rank hRank)

theorem prefixCountFirstHitReturnTailMonodromyGoal_of_rankEquiv
    (hEquiv : PrefixCountFirstHitReturnTailRankEquivGoal) :
    PrefixCountFirstHitReturnTailMonodromyGoal :=
  prefixCountFirstHitReturnTailMonodromyGoal_of_rank
    (prefixCountFirstHitReturnTailRankGoal_of_rankEquiv hEquiv)

theorem prefixCountFirstHitReturnTailMonodromyGoal_of_cycleCoordinate
    (hCycle : PrefixCountFirstHitReturnTailCycleCoordinateGoal) :
    PrefixCountFirstHitReturnTailMonodromyGoal :=
  prefixCountFirstHitReturnTailMonodromyGoal_of_rankEquiv
    (prefixCountFirstHitReturnTailRankEquivGoal_of_cycleCoordinate hCycle)

noncomputable theorem prefixCountFirstHitReturnTailCycleCoordinateGoal_of_monodromy
    (hTail : PrefixCountFirstHitReturnTailMonodromyGoal) :
    PrefixCountFirstHitReturnTailCycleCoordinateGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L c
  have hcard :
      Fintype.card (Fin (d - 2) → ZMod m) = m ^ (d - 2) := by
    exact Shared.card_zmodVector (d - 2) m
  have hm1 : 1 < m := by omega
  have hexp : d - 2 ≠ 0 := by omega
  have hn : 1 < m ^ (d - 2) := one_lt_pow₀ hm1 hexp
  exact
    Shared.CycleCoordinate.ofFiniteSingleCycle
      (f := prefixCountFirstHitReturnTailMonodromy hd2 L c)
      hcard hn
      (hTail hd2 hdodd hd5 hmodd hdm hC L c)

theorem prefixCountFirstHitReturnTailRankEquivGoal_of_monodromy
    (hTail : PrefixCountFirstHitReturnTailMonodromyGoal) :
    PrefixCountFirstHitReturnTailRankEquivGoal :=
  prefixCountFirstHitReturnTailRankEquivGoal_of_cycleCoordinate
    (prefixCountFirstHitReturnTailCycleCoordinateGoal_of_monodromy hTail)

theorem prefixCountFirstHitReturnTailRankGoal_of_monodromy
    (hTail : PrefixCountFirstHitReturnTailMonodromyGoal) :
    PrefixCountFirstHitReturnTailRankGoal :=
  prefixCountFirstHitReturnTailRankGoal_of_rankEquiv
    (prefixCountFirstHitReturnTailRankEquivGoal_of_monodromy hTail)

theorem prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_monodromy
    (hTail : PrefixCountFirstHitReturnTailMonodromyGoal) :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L c tail₁ tail₂
  exact (hTail hd2 hdodd hd5 hmodd hdm hC L c).2 tail₁ tail₂

theorem prefixCountFirstHitReturnTailMonodromyGoal_iff_orbitGoal :
    PrefixCountFirstHitReturnTailMonodromyGoal ↔
      PrefixCountFirstHitReturnTailMonodromyOrbitGoal :=
  ⟨prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_monodromy,
    prefixCountFirstHitReturnTailMonodromyGoal_of_orbit⟩

theorem prefixCountFirstHitReturnTailMonodromyGoal_iff_rankGoal :
    PrefixCountFirstHitReturnTailMonodromyGoal ↔
      PrefixCountFirstHitReturnTailRankGoal :=
  ⟨prefixCountFirstHitReturnTailRankGoal_of_monodromy,
    prefixCountFirstHitReturnTailMonodromyGoal_of_rank⟩

theorem prefixCountFirstHitReturnTailMonodromyGoal_iff_rankEquivGoal :
    PrefixCountFirstHitReturnTailMonodromyGoal ↔
      PrefixCountFirstHitReturnTailRankEquivGoal :=
  ⟨prefixCountFirstHitReturnTailRankEquivGoal_of_monodromy,
    prefixCountFirstHitReturnTailMonodromyGoal_of_rankEquiv⟩

theorem prefixCountFirstHitReturnTailMonodromyGoal_iff_cycleCoordinateGoal :
    PrefixCountFirstHitReturnTailMonodromyGoal ↔
      PrefixCountFirstHitReturnTailCycleCoordinateGoal :=
  ⟨prefixCountFirstHitReturnTailCycleCoordinateGoal_of_monodromy,
    prefixCountFirstHitReturnTailMonodromyGoal_of_cycleCoordinate⟩

theorem prefixCountFirstHitHeadTailSectionMonodromyGoal_of_returnTailOrbit
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal) :
    PrefixCountFirstHitHeadTailSectionMonodromyGoal :=
  prefixCountFirstHitHeadTailSectionMonodromyGoal_of_returnTailMonodromy
    (prefixCountFirstHitReturnTailMonodromyGoal_of_orbit hOrbit)

theorem prefixCountFirstHitHeadTailMonodromyGoal_of_sectionMonodromy
    (hSection : PrefixCountFirstHitHeadTailSectionMonodromyGoal) :
    PrefixCountFirstHitHeadTailMonodromyGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L c
  exact ⟨
    prefixCountFirstHitReturnFiberStep_bijective
      hd2 hdodd hd5 hmodd hdm hC L c,
    hSection hd2 hdodd hd5 hmodd hdm hC L c⟩

theorem prefixCountFirstHitCanonicalReturnsSingleCycleGoal_of_sectionMonodromy
    (hSection : PrefixCountFirstHitHeadTailSectionMonodromyGoal) :
    PrefixCountFirstHitCanonicalReturnsSingleCycleGoal :=
  prefixCountFirstHitCanonicalReturnsSingleCycleGoal_of_headTailMonodromy
    (prefixCountFirstHitHeadTailMonodromyGoal_of_sectionMonodromy hSection)

theorem prefixCountFirstHitCanonicalReturnsSingleCycleGoal_of_returnTailMonodromy
    (hTail : PrefixCountFirstHitReturnTailMonodromyGoal) :
    PrefixCountFirstHitCanonicalReturnsSingleCycleGoal :=
  prefixCountFirstHitCanonicalReturnsSingleCycleGoal_of_sectionMonodromy
    (prefixCountFirstHitHeadTailSectionMonodromyGoal_of_returnTailMonodromy
      hTail)

theorem prefixCountFirstHitCanonicalScheduleAuxGoal_of_returns
    (hReturn : PrefixCountFirstHitCanonicalReturnsSingleCycleGoal) :
    PrefixCountFirstHitCanonicalScheduleAuxGoal :=
  ⟨prefixCountFirstHitCanonicalLayerBijectiveGoal, hReturn⟩

theorem prefixCountRootLayerEquiv_step {d m : Nat} (hd1 : 1 ≤ d)
    (i : Fin d) (tw : ZMod m × PrefixCountRootState d m) :
    prefixCountRootLayerEquiv d m hd1
        (tw.1 + 1, prefixCountRootStep d m i tw.2)
      =
      prefixCountRootLayerEquiv d m hd1 tw + Shared.torusBasis d m i := by
  rw [prefixCountRootStep_eq_succ_cast hd1 i tw.2]
  unfold prefixCountRootLayerEquiv
  simp only [Equiv.trans_apply]
  rw [prefixCountRootLayerEquivSucc_step]
  funext k
  simp [Equiv.arrowCongr, Shared.torusBasis]

def PrefixCountRootFlatReturnGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    PrefixCount.LayerPermCounts d m (C.toMatrix hd2) →
    Shared.RootFlatReturnCriterion
      (Fin d) (Fin d) (PrefixCountRootState d m) m

def PrefixCountRootFlatCanonicalReturnGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    PrefixCount.LayerPermCounts d m (C.toMatrix hd2) →
    ∃ cert : Shared.RootFlatCertificate
      (Fin d) (Fin d) (PrefixCountRootState d m) m,
      cert.schedule.step = prefixCountRootStep d m

def PrefixCountRootFlatCanonicalScheduleCriterionGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    PrefixCount.LayerPermCounts d m (C.toMatrix hd2) →
    ∃ S : Shared.RootFlatSchedule
        (Fin d) (Fin d) (PrefixCountRootState d m) m,
      S.step = prefixCountRootStep d m ∧
      S.rowLatin ∧ S.layerBijective ∧ S.returnsSingleCycle

theorem prefixCountRootFlatCanonicalScheduleCriterionGoal_of_firstHit_aux
    (hAux : PrefixCountFirstHitCanonicalScheduleAuxGoal) :
    PrefixCountRootFlatCanonicalScheduleCriterionGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L
  refine ⟨prefixCountFirstHitCanonicalSchedule hd2 L,
    prefixCountFirstHitCanonicalSchedule_step hd2 L,
    prefixCountFirstHitCanonicalSchedule_rowLatin hd2 L,
    hAux.1 hd2 hdodd hd5 hmodd hdm hC L,
    hAux.2 hd2 hdodd hd5 hmodd hdm hC L⟩

theorem prefixCountRootFlatCanonicalScheduleCriterionGoal_of_firstHit_returns
    (hReturn : PrefixCountFirstHitCanonicalReturnsSingleCycleGoal) :
    PrefixCountRootFlatCanonicalScheduleCriterionGoal :=
  prefixCountRootFlatCanonicalScheduleCriterionGoal_of_firstHit_aux
    (prefixCountFirstHitCanonicalScheduleAuxGoal_of_returns hReturn)

theorem prefixCountRootFlatCanonicalScheduleCriterionGoal_of_sectionMonodromy
    (hSection : PrefixCountFirstHitHeadTailSectionMonodromyGoal) :
    PrefixCountRootFlatCanonicalScheduleCriterionGoal :=
  prefixCountRootFlatCanonicalScheduleCriterionGoal_of_firstHit_returns
    (prefixCountFirstHitCanonicalReturnsSingleCycleGoal_of_sectionMonodromy
      hSection)

theorem prefixCountRootFlatCanonicalReturnGoal_of_scheduleCriterion
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal) :
    PrefixCountRootFlatCanonicalReturnGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L
  rcases hSchedule hd2 hdodd hd5 hmodd hdm hC L with
    ⟨S, hStep, hRow, hLayer, hReturn⟩
  exact ⟨{
    schedule := S
    rowLatin := hRow
    layerBijective := hLayer
    returnsSingleCycle := hReturn
  }, hStep⟩

theorem prefixCountRootFlatCanonicalScheduleCriterionGoal_of_return
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    PrefixCountRootFlatCanonicalScheduleCriterionGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L
  rcases hReturn hd2 hdodd hd5 hmodd hdm hC L with ⟨cert, hStep⟩
  exact ⟨cert.schedule, hStep, cert.rowLatin, cert.layerBijective,
    cert.returnsSingleCycle⟩

theorem prefixCountRootFlatCanonicalReturnGoal_iff_scheduleCriterion :
    PrefixCountRootFlatCanonicalReturnGoal ↔
      PrefixCountRootFlatCanonicalScheduleCriterionGoal :=
  ⟨prefixCountRootFlatCanonicalScheduleCriterionGoal_of_return,
    prefixCountRootFlatCanonicalReturnGoal_of_scheduleCriterion⟩

def PrefixCountRootFlatCayleyLiftGoal : Prop :=
  ∀ {d m : Nat} [NeZero m],
    2 ≤ d → Odd d → 5 ≤ d → Odd m → d ≤ m →
    Shared.RootFlatLayeredHamiltonDecomposition
      (Fin d) (Fin d) (PrefixCountRootState d m) m →
    StandardCayleySolved d m

def RootFlatCayleyStepCompatible {d m : Nat} [NeZero m] {RootState : Type*}
    (D : Shared.RootFlatLayeredDecomposition (Fin d) (Fin d) RootState m)
    (E : ZMod m × RootState ≃ Shared.TorusVertex d m) : Prop :=
  ∀ c : Fin d, ∀ tw : ZMod m × RootState,
    E (D.schedule.fullStep c tw) =
      Shared.cayleyColorStep
        (fun c x => D.schedule.dir (E.symm x).1 (E.symm x).2 c)
        c (E tw)

def PrefixCountRootFlatEquivLiftGoal : Prop :=
  ∀ {d m : Nat} [NeZero m],
    2 ≤ d → Odd d → 5 ≤ d → Odd m → d ≤ m →
    (D : Shared.RootFlatLayeredDecomposition
      (Fin d) (Fin d) (PrefixCountRootState d m) m) →
    ∃ E : ZMod m × PrefixCountRootState d m ≃ Shared.TorusVertex d m,
      RootFlatCayleyStepCompatible D E

def D11SmallModulusFromD5BaseGoal : Prop :=
  ∀ {m : Nat}, 3 ≤ m → Odd m → m < 11 →
    StandardCayleySolved 5 m →
    StandardCayleySolved 11 m

def OddCoreSmallModulusOfBaseGoal : Prop :=
  ∀ {d m b : Nat},
    Odd d → 13 ≤ d →
    Odd m → 3 ≤ m → m < d →
    StandardCayleySolved b m →
    2 * b < d ∧ d ≤ 3 * b →
    StandardCayleySolved d m

def OddCoreSmallModulusOfUnitPacketsGoal : Prop :=
  ∀ {d m b : Nat},
    Odd d → 13 ≤ d →
    Odd m → 3 ≤ m → m < d →
    StandardCayleySolved b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = d →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    StandardCayleySolved d m

def OddCoreSmallModulusUnitPacketLiftGoal : Prop :=
  ∀ {d m b : Nat},
    Odd d → 11 ≤ d →
    Odd m → 3 ≤ m → m < d →
    StandardCayleySolved b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = d →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    StandardCayleySolved d m

def OddCoreSmallModulusSlackPacketLiftGoal : Prop :=
  ∀ {d m b : Nat},
    Odd d → 11 ≤ d →
    Odd m → 3 ≤ m → m < d →
    StandardCayleySolved b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = d →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    d - b > b →
    m ^ b > m * d * (d - b) →
    StandardCayleySolved d m

def OddCoreSmallModulusSlackPacketLiftAddGoal : Prop :=
  ∀ {d m b T : Nat},
    Odd d → 11 ≤ d →
    Odd m → 3 ≤ m → m < d →
    StandardCayleySolved b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = d →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    d = b + T →
    T > b →
    m ^ b > m * d * T →
    StandardCayleySolved d m

theorem oddCoreSmallModulusSlackPacketLiftAddGoal_of_slackPacketLift
    (hLift : OddCoreSmallModulusSlackPacketLiftGoal) :
    OddCoreSmallModulusSlackPacketLiftAddGoal := by
  intro d m b T hdodd hd11 hmodd hm3 hmd hbSolved packets
    hlen hsum hpacketSum hpacketUnits hdEq hT hSlack
  have hTail : d - b > b := by omega
  have hSlack' : m ^ b > m * d * (d - b) := by
    have hTsub : T = d - b := by omega
    simpa [hTsub] using hSlack
  exact hLift hdodd hd11 hmodd hm3 hmd hbSolved packets
    hlen hsum hpacketSum hpacketUnits hTail hSlack'

theorem oddCoreSmallModulusSlackPacketLiftGoal_of_add
    (hLift : OddCoreSmallModulusSlackPacketLiftAddGoal) :
    OddCoreSmallModulusSlackPacketLiftGoal := by
  intro d m b hdodd hd11 hmodd hm3 hmd hbSolved packets
    hlen hsum hpacketSum hpacketUnits hTail hSlack
  have hdEq : d = b + (d - b) := by omega
  exact hLift hdodd hd11 hmodd hm3 hmd hbSolved packets
    hlen hsum hpacketSum hpacketUnits hdEq hTail hSlack

theorem oddCoreSmallModulusSlackPacketLiftGoal_iff_add :
    OddCoreSmallModulusSlackPacketLiftGoal ↔
      OddCoreSmallModulusSlackPacketLiftAddGoal :=
  ⟨oddCoreSmallModulusSlackPacketLiftAddGoal_of_slackPacketLift,
    oddCoreSmallModulusSlackPacketLiftGoal_of_add⟩

def OddSuccessorSmallModulusSlackPacketLiftAddGoal : Prop :=
  ∀ {b m T : Nat},
    5 ≤ b →
    Odd m → 3 ≤ m → m < b + T →
    StandardCayleySolved b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    T = b + 1 →
    m ^ b > m * (b + T) * T →
    StandardCayleySolved (b + T) m

theorem oddSuccessorSmallModulusSlackPacketLiftAddGoal_of_coreAdd
    (hLift : OddCoreSmallModulusSlackPacketLiftAddGoal) :
    OddSuccessorSmallModulusSlackPacketLiftAddGoal := by
  intro b m T hb5 hmodd hm3 hmd hbSolved packets
    hlen hsum hpacketSum hpacketUnits hT hSlack
  have hdodd : Odd (b + T) := by
    rw [hT]
    exact ⟨b, by omega⟩
  have hd11 : 11 ≤ b + T := by omega
  have hTgt : T > b := by omega
  exact hLift
    (d := b + T) (m := m) (b := b) (T := T)
    hdodd hd11 hmodd hm3 hmd hbSolved packets
    hlen hsum hpacketSum hpacketUnits rfl hTgt hSlack

def OddSuccessorSmallModulusBaseTailGoal : Prop :=
  ∀ {b m : Nat},
    5 ≤ b →
    Odd m → 3 ≤ m →
    m < 2 * b + 1 →
    StandardCayleySolved b m →
    StandardCayleySolved (2 * b + 1) m

def OddCoreSmallBaseSlackWitnessGoal : Prop :=
  ∀ {d m : Nat},
    Odd d → 13 ≤ d →
    Odd m → 3 ≤ m → m < d →
    ∃ w : SmallBaseUnitPacketWitness d m,
      d - w.b > w.b ∧
      m ^ w.b > m * d * (d - w.b)

theorem oddCoreSmallBaseSlackWitnessGoal_of_seed_semigroup :
    OddCoreSmallBaseSlackWitnessGoal := by
  intro d m hdodd hd13 hmodd hm3 hmd
  rcases seed_semigroup_base_available_with_hall_slack
      hdodd hd13 hm3 hmd with
    ⟨b, hbSeed, hbLow, hbHigh, hTail, hSlack⟩
  have hbRange : 2 * b < d ∧ d ≤ 3 * b := ⟨hbLow, hbHigh⟩
  have hpackets :=
    _root_.RoundComposite.unitCarryPackets_spec hm3 hmodd hbRange
  refine ⟨{
    b := b
    seed := hbSeed
    range := hbRange
    packets := _root_.RoundComposite.unitCarryPackets m b d
    packets_length := hpackets.1
    packets_total_length := hpackets.2.1
    packet_sum := fun packet hp => (hpackets.2.2 packet hp).1
    packet_units := fun packet hp a ha => (hpackets.2.2 packet hp).2 a ha
  }, hTail, hSlack⟩

theorem oddCoreHighModulusPrefixCount_of_goal
    (hHigh : OddCoreHighModulusPrefixCountGoal) :
    OddCoreHighModulusPrefixCount StandardCayleySolved := by
  intro d m hdodd hd5 _hm3 hmodd hdm
  exact hHigh hdodd hd5 hmodd hdm

theorem oddSuccessorHighModulusPrefixCountGoal_of_high
    (hHigh : OddCoreHighModulusPrefixCountGoal) :
    OddSuccessorHighModulusPrefixCountGoal := by
  intro b m hb5 hmodd hdm
  exact hHigh ⟨b, rfl⟩ (by omega) hmodd hdm

theorem oddSuccessorClosureGoal_of_high_and_successorSmall
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal := by
  intro b m hb5 hmodd hm3 hbSolved
  by_cases hmd : 2 * b + 1 ≤ m
  · exact hHigh ⟨b, rfl⟩ (by omega) hmodd hmd
  · exact hSmall hb5 hmodd hm3 (lt_of_not_ge hmd) hbSolved

theorem oddSuccessorClosureGoal_of_successorHigh_and_successorSmall
    (hHigh : OddSuccessorHighModulusPrefixCountGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal := by
  intro b m hb5 hmodd hm3 hbSolved
  by_cases hmd : 2 * b + 1 ≤ m
  · exact hHigh hb5 hmodd hmd
  · exact hSmall hb5 hmodd hm3 (lt_of_not_ge hmd) hbSolved

theorem odd_successor_closure_of_high_and_successorSmall
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_high_and_successorSmall hHigh hSmall)
    hb5 hmodd hm3 hb

theorem odd_successor_closure_of_successorHigh_and_successorSmall
    (hHigh : OddSuccessorHighModulusPrefixCountGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_successorHigh_and_successorSmall hHigh hSmall)
    hb5 hmodd hm3 hb

theorem oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLift
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal) :
    OddSuccessorSmallModulusBaseTailGoal := by
  intro b m hb5 hmodd hm3 hmSmall hbSolved
  have hdodd : Odd (2 * b + 1) := ⟨b, rfl⟩
  have hd11 : 11 ≤ 2 * b + 1 := by omega
  have hRange : 2 * b < 2 * b + 1 ∧ 2 * b + 1 ≤ 3 * b := by omega
  have hpackets :=
    _root_.RoundComposite.unitCarryPackets_spec
      (b := b) (d := 2 * b + 1) (m := m) hm3 hmodd hRange
  exact hSmallPacket
    (d := 2 * b + 1) (b := b)
    hdodd hd11 hmodd hm3 hmSmall hbSolved
    (_root_.RoundComposite.unitCarryPackets m b (2 * b + 1))
    hpackets.1
    hpackets.2.1
    (fun packet hp => (hpackets.2.2 packet hp).1)
    (fun packet hp a ha => (hpackets.2.2 packet hp).2 a ha)
    (by omega)
    (_root_.RoundComposite.successor_hall_slack hb5 hm3)

theorem odd_successor_small_modulus_base_tail_of_slackPacketLift
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hmSmall : m < 2 * b + 1)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLift hSmallPacket)
    hb5 hmodd hm3 hmSmall hb

theorem oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd
    (hSmallPacket : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddSuccessorSmallModulusBaseTailGoal := by
  intro b m hb5 hmodd hm3 hmSmall hbSolved
  have hRange :
      2 * b < b + (b + 1) ∧ b + (b + 1) ≤ 3 * b := by
    omega
  have hpackets :=
    _root_.RoundComposite.unitCarryPackets_spec
      (b := b) (d := b + (b + 1)) (m := m) hm3 hmodd hRange
  have hmSmall' : m < b + (b + 1) := by omega
  have hSlack : m ^ b > m * (b + (b + 1)) * (b + 1) := by
    have h0 := _root_.RoundComposite.successor_hall_slack hb5 hm3
    have hsum : b + (b + 1) = 2 * b + 1 := by omega
    have htail : (2 * b + 1) - b = b + 1 := by omega
    simpa [hsum, htail] using h0
  have hSolved : StandardCayleySolved (b + (b + 1)) m :=
    hSmallPacket
      (b := b) (m := m) (T := b + 1)
      hb5 hmodd hm3 hmSmall' hbSolved
      (_root_.RoundComposite.unitCarryPackets m b (b + (b + 1)))
      hpackets.1
      hpackets.2.1
      (fun packet hp => (hpackets.2.2 packet hp).1)
      (fun packet hp a ha => (hpackets.2.2 packet hp).2 a ha)
      rfl
      hSlack
  simpa [show b + (b + 1) = 2 * b + 1 by omega] using hSolved

theorem odd_successor_small_modulus_base_tail_of_slackPacketLiftAdd
    (hSmallPacket : OddSuccessorSmallModulusSlackPacketLiftAddGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hmSmall : m < 2 * b + 1)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmallPacket)
    hb5 hmodd hm3 hmSmall hb

theorem oddSuccessorClosureGoal_of_high_and_slackPacketLift
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall hHigh
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLift hSmallPacket)

theorem odd_successor_closure_of_high_and_slackPacketLift
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_high_and_slackPacketLift hHigh hSmallPacket)
    hb5 hmodd hm3 hb

theorem oddSuccessorClosureGoal_of_high_and_slackPacketLiftAdd
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmallPacket : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall hHigh
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmallPacket)

theorem odd_successor_closure_of_high_and_slackPacketLiftAdd
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmallPacket : OddSuccessorSmallModulusSlackPacketLiftAddGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_high_and_slackPacketLiftAdd hHigh hSmallPacket)
    hb5 hmodd hm3 hb

theorem oddCoreHighModulusPrefixCountGoal_of_prefixCount
    (hParts : PrefixCount.AdmissiblePartsCountBranchGoal)
    (hLayers : PrefixCountLayerRealizationGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal := by
  intro d m hdodd hd5 hmodd hdm
  have hd2 : 2 ≤ d := by omega
  rcases hParts hdodd hmodd hd5 hdm with ⟨C, hC⟩
  rcases hLayers hd2 C hC with ⟨L⟩
  exact hGeom hd2 hdodd hd5 hmodd hdm hC L

theorem prefixCountGeometricCriterionGoal_of_rootFlat
    (hReturn : PrefixCountRootFlatReturnGoal)
    (hLift : PrefixCountRootFlatCayleyLiftGoal) :
    PrefixCountGeometricCriterionGoal := by
  intro d m hd2 C hdodd hd5 hmodd hdm hC L
  haveI : NeZero m := ⟨by omega⟩
  rcases hReturn hd2 hdodd hd5 hmodd hdm hC L with ⟨cert⟩
  exact hLift hd2 hdodd hd5 hmodd hdm
    (Shared.rootFlatLayeredDecomposition_of_certificate cert)

theorem standardCayleySolved_of_rootFlatLayeredEquiv
    {d m : Nat} [NeZero m] {RootState : Type*}
    (D : Shared.RootFlatLayeredDecomposition (Fin d) (Fin d) RootState m)
    (E : ZMod m × RootState ≃ Shared.TorusVertex d m)
    (hCompat : RootFlatCayleyStepCompatible D E) :
    StandardCayleySolved d m := by
  let colorDir : Shared.TorusColor d → Shared.TorusVertex d m →
      Shared.TorusDirection d :=
    fun c x => D.schedule.dir (E.symm x).1 (E.symm x).2 c
  refine ⟨{
    colorDir := colorDir
    edgePartition := ?_
    colorHamiltonian := ?_
  }⟩
  · intro x i
    rcases D.edgePartition (E.symm x).1 (E.symm x).2 i with
      ⟨c, hc, huniq⟩
    exact ⟨c, hc, fun c' hc' => huniq c' hc'⟩
  · intro c
    refine Shared.single_cycle_of_equiv_conj E
      (Shared.cayleyColorStep colorDir c)
      (D.schedule.fullStep c)
      (D.colorHamiltonian c) ?_
    intro tw
    calc
      E.symm (Shared.cayleyColorStep colorDir c (E tw))
          = E.symm (E (D.schedule.fullStep c tw)) := by
              rw [hCompat c tw]
      _ = D.schedule.fullStep c tw := by simp

theorem standardCayleySolved_of_rootFlatLayered_standardStepSucc
    {n m : Nat} [NeZero m]
    (D : Shared.RootFlatLayeredDecomposition
      (Fin (n + 1)) (Fin (n + 1)) (Fin n → ZMod m) m)
    (hStep : D.schedule.step = prefixCountRootStepSucc) :
    StandardCayleySolved (n + 1) m := by
  refine standardCayleySolved_of_rootFlatLayeredEquiv D
    (prefixCountRootLayerEquivSucc n m) ?_
  intro c tw
  simp [Shared.RootFlatSchedule.fullStep, Shared.RootFlatSchedule.layerMap,
    Shared.cayleyColorStep, hStep, prefixCountRootLayerEquivSucc_step]

theorem standardCayleySolved_of_rootFlatLayered_standardStep
    {d m : Nat} [NeZero m] (hd1 : 1 ≤ d)
    (D : Shared.RootFlatLayeredDecomposition
      (Fin d) (Fin d) (PrefixCountRootState d m) m)
    (hStep : D.schedule.step = prefixCountRootStep d m) :
    StandardCayleySolved d m := by
  refine standardCayleySolved_of_rootFlatLayeredEquiv D
    (prefixCountRootLayerEquiv d m hd1) ?_
  intro c tw
  simp [Shared.RootFlatSchedule.fullStep, Shared.RootFlatSchedule.layerMap,
    Shared.cayleyColorStep, hStep, prefixCountRootLayerEquiv_step]

theorem prefixCountGeometricCriterionGoal_of_rootFlatCanonical
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    PrefixCountGeometricCriterionGoal := by
  intro d m hd2 C hdodd hd5 hmodd hdm hC L
  haveI : NeZero m := ⟨by omega⟩
  rcases hReturn hd2 hdodd hd5 hmodd hdm hC L with ⟨cert, hStep⟩
  let D : Shared.RootFlatLayeredDecomposition
      (Fin d) (Fin d) (PrefixCountRootState d m) m := {
    schedule := cert.schedule
    edgePartition := cert.schedule.edgePartition_of_rowLatin cert.rowLatin
    colorHamiltonian := cert.schedule.fullStepsHamiltonian_of_return
      cert.layerBijective cert.returnsSingleCycle
  }
  exact standardCayleySolved_of_rootFlatLayered_standardStep
    (by omega : 1 ≤ d) D hStep

theorem prefixCountRootFlatCayleyLiftGoal_of_equiv
    (hEquiv : PrefixCountRootFlatEquivLiftGoal) :
    PrefixCountRootFlatCayleyLiftGoal := by
  intro d m _inst hd2 hdodd hd5 hmodd hdm hRoot
  rcases hRoot with ⟨D⟩
  rcases hEquiv hd2 hdodd hd5 hmodd hdm D with ⟨E, hCompat⟩
  exact standardCayleySolved_of_rootFlatLayeredEquiv D E hCompat

theorem prefixCountLayerRealizationGoal_of_matrixLayerRealization
    (hMatrix : PrefixCount.MatrixLayerRealizationGoal) :
    PrefixCountLayerRealizationGoal := by
  intro d m hd2 C hC
  exact PrefixCount.layerRealization_of_matrixLayerRealizationGoal
    hMatrix hd2 C hC

theorem prefixCountLayerRealizationGoal_of_balancedMatrixLayerRealization
    (hBalanced : PrefixCount.BalancedMatrixLayerRealizationGoal) :
    PrefixCountLayerRealizationGoal :=
  prefixCountLayerRealizationGoal_of_matrixLayerRealization
    (PrefixCount.matrixLayerRealizationGoal_of_balanced hBalanced)

theorem prefixCountLayerRealizationGoal : PrefixCountLayerRealizationGoal :=
  prefixCountLayerRealizationGoal_of_matrixLayerRealization
    PrefixCount.matrixLayerRealizationGoal

theorem oddCoreHighModulusPrefixCountGoal_of_parts_and_geometry
    (hParts : PrefixCount.AdmissiblePartsCountBranchGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_prefixCount
    hParts prefixCountLayerRealizationGoal hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_transports_and_geometry
    (hQge2 : PrefixCount.TransportQge2Goal)
    (hQeq1 : PrefixCount.TransportQeq1Goal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_parts_and_geometry
    (PrefixCount.admissiblePartsCountBranchGoal_of_transports hQge2 hQeq1)
    hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_margins_and_geometry
    (hQge2 : PrefixCount.MarginTransportQge2Goal)
    (hQeq1 : PrefixCount.MarginTransportQeq1Goal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_transports_and_geometry
    (PrefixCount.transportQge2Goal_of_margin hQge2)
    (PrefixCount.transportQeq1Goal_of_margin hQeq1)
    hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Margin_qeq1PlusFamily_and_geometry
    (hQge2 : PrefixCount.MarginTransportQge2Goal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_margins_and_geometry
    hQge2
    (PrefixCount.marginTransportQeq1Goal_of_compatible
      (PrefixCount.marginTransportQeq1CompatibleGoal_of_matchedPMOne
        (PrefixCount.marginTransportQeq1MatchedPMOneGoal_of_plusFamily hQeq1)))
    hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Margin_qeq1PlusFamily_and_rootFlatCanonical
    (hQge2 : PrefixCount.MarginTransportQge2Goal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Margin_qeq1PlusFamily_and_geometry
    hQge2 hQeq1
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Compat_qeq1PlusFamily_and_geometry
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Margin_qeq1PlusFamily_and_geometry
    (PrefixCount.marginTransportQge2Goal_of_compatible hQge2)
    hQeq1 hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Compat_qeq1PlusFamily_and_rootFlatCanonical
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Compat_qeq1PlusFamily_and_geometry
    hQge2 hQeq1
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Compat_qeq1Compat_and_geometry
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1CompatibleGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_margins_and_geometry
    (PrefixCount.marginTransportQge2Goal_of_compatible hQge2)
    (PrefixCount.marginTransportQeq1Goal_of_compatible hQeq1)
    hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Compat_qeq1Compat_and_rootFlatCanonical
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1CompatibleGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Compat_qeq1Compat_and_geometry
    hQge2 hQeq1
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)

theorem oddCoreHighModulusPrefixCountGoal_of_qge2OrdinaryCore_qeq1Compat_and_rootFlatCanonical
    (hQge2 : PrefixCount.OrdinaryQge2SignedCoreGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1CompatibleGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Compat_qeq1Compat_and_rootFlatCanonical
    (PrefixCount.marginTransportQge2CompatibleGoal_of_ordinaryQge2SignedCore
      hQge2)
    hQeq1 hReturn

theorem oddCoreHighModulusPrefixCountGoal_of_ordinarySignedCores_and_geometry
    (hQge2 : PrefixCount.OrdinaryQge2SignedCoreGoal)
    (hQeq1 : PrefixCount.OrdinaryQeq1SignedCoreGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Compat_qeq1Compat_and_geometry
    (PrefixCount.marginTransportQge2CompatibleGoal_of_ordinaryQge2SignedCore
      hQge2)
    (PrefixCount.marginTransportQeq1CompatibleGoal_of_ordinaryQeq1SignedCore
      hQeq1)
    hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2PlanMatrix_qeq1Core_and_geometry
    (hQge2Plan : PrefixCount.OrdinaryQge2PlanGoal)
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1 : PrefixCount.OrdinaryQeq1SignedCoreGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_ordinarySignedCores_and_geometry
    (PrefixCount.ordinaryQge2SignedCoreGoal_of_plan_and_matrix
      hQge2Plan hQge2Matrix)
    hQeq1 hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Core_and_geometry
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1 : PrefixCount.OrdinaryQeq1SignedCoreGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2PlanMatrix_qeq1Core_and_geometry
    PrefixCount.ordinaryQge2PlanGoal hQge2Matrix hQeq1 hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Canonical_and_geometry
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1CanonicalMatrixGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Core_and_geometry
    hQge2Matrix
    (PrefixCount.ordinaryQeq1SignedCoreGoal_of_canonicalMatrix hQeq1Matrix)
    hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1Canonical_and_geometry
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1CanonicalMatrixGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Canonical_and_geometry
    (PrefixCount.ordinaryQge2SignedMatrixGoal_of_signedSeedClosure
      hQge2Closure)
    hQeq1Matrix hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1Correction_and_geometry
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Correction : PrefixCount.OrdinaryQeq1CanonicalCorrectionGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1Canonical_and_geometry
    hQge2Closure
    (PrefixCount.ordinaryQeq1CanonicalMatrixGoal_of_correction
      hQeq1Correction)
    hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_planMatrixSignedCores_and_geometry
    (hQge2Plan : PrefixCount.OrdinaryQge2PlanGoal)
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1Plan : PrefixCount.OrdinaryQeq1PlanGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1SignedMatrixGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2PlanMatrix_qeq1Core_and_geometry
    hQge2Plan hQge2Matrix
    (PrefixCount.ordinaryQeq1SignedCoreGoal_of_plan_and_matrix
      hQeq1Plan hQeq1Matrix)
    hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2PlanMatrix_qeq1Matrix_and_geometry
    (hQge2Plan : PrefixCount.OrdinaryQge2PlanGoal)
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1SignedMatrixGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_planMatrixSignedCores_and_geometry
    hQge2Plan hQge2Matrix
    PrefixCount.ordinaryQeq1PlanGoal hQeq1Matrix hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedMatrix_qeq1Matrix_and_geometry
    (hQge2Seed : PrefixCount.OrdinaryQge2SeedGoal)
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1SignedMatrixGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2PlanMatrix_qeq1Matrix_and_geometry
    (PrefixCount.ordinaryQge2PlanGoal_of_seed hQge2Seed)
    hQge2Matrix hQeq1Matrix hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Matrix_and_geometry
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1SignedMatrixGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedMatrix_qeq1Matrix_and_geometry
    PrefixCount.ordinaryQge2SeedGoal hQge2Matrix hQeq1Matrix hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_ordinarySignedCores_and_rootFlatCanonical
    (hQge2 : PrefixCount.OrdinaryQge2SignedCoreGoal)
    (hQeq1 : PrefixCount.OrdinaryQeq1SignedCoreGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2OrdinaryCore_qeq1Compat_and_rootFlatCanonical
    hQge2
    (PrefixCount.marginTransportQeq1CompatibleGoal_of_ordinaryQeq1SignedCore
      hQeq1)
    hReturn

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Core_and_rootFlatCanonical
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1 : PrefixCount.OrdinaryQeq1SignedCoreGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Core_and_geometry
    hQge2Matrix hQeq1
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Canonical_and_rootFlatCanonical
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1CanonicalMatrixGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Canonical_and_geometry
    hQge2Matrix hQeq1Matrix
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1Canonical_and_rootFlatCanonical
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1CanonicalMatrixGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1Canonical_and_geometry
    hQge2Closure hQeq1Matrix
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1Correction_and_rootFlatCanonical
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Correction : PrefixCount.OrdinaryQeq1CanonicalCorrectionGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1Correction_and_geometry
    hQge2Closure hQeq1Correction
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1CorrectionData_and_rootFlatCanonical
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Data : PrefixCount.OrdinaryQeq1CanonicalCorrectionDataGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1Correction_and_rootFlatCanonical
    hQge2Closure
    (PrefixCount.ordinaryQeq1CanonicalCorrectionGoal_of_dataGoal hQeq1Data)
    hReturn

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxMatching_and_rootFlatCanonical
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Aux : PrefixCount.OrdinaryQeq1AuxMatrixGoal)
    (hQeq1Match : PrefixCount.OrdinaryQeq1SpecialMatchingGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1CorrectionData_and_rootFlatCanonical
    hQge2Closure
    (PrefixCount.ordinaryQeq1CanonicalCorrectionDataGoal_of_auxMatrix_and_specialMatching
      hQeq1Aux hQeq1Match)
    hReturn

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxSpecialMatchingData_and_rootFlatCanonical
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Data : PrefixCount.OrdinaryQeq1AuxSpecialMatchingDataGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1CorrectionData_and_rootFlatCanonical
    hQge2Closure
    (PrefixCount.ordinaryQeq1CanonicalCorrectionDataGoal_of_auxSpecialMatchingData
      hQeq1Data)
    hReturn

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxPRowSpecialMatchingData_and_rootFlatCanonical
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Data : PrefixCount.OrdinaryQeq1AuxPRowSpecialMatchingDataGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxSpecialMatchingData_and_rootFlatCanonical
    hQge2Closure
    (PrefixCount.ordinaryQeq1AuxSpecialMatchingDataGoal_of_pRowSpecialMatchingData
      hQeq1Data)
    hReturn

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxTargetHallData_and_rootFlatCanonical
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Data : PrefixCount.OrdinaryQeq1AuxTargetHallDataGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxPRowSpecialMatchingData_and_rootFlatCanonical
    hQge2Closure
    (PrefixCount.ordinaryQeq1AuxPRowSpecialMatchingDataGoal_of_targetHallData
      hQeq1Data)
    hReturn

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1DegreeSpecialMatching_and_rootFlatCanonical
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Match : PrefixCount.OrdinaryQeq1DegreeSpecialMatchingGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxSpecialMatchingData_and_rootFlatCanonical
    hQge2Closure
    (PrefixCount.ordinaryQeq1AuxSpecialMatchingDataGoal_of_degreeSpecialMatching
      hQeq1Match)
    hReturn

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1DegreeMatching_and_rootFlatCanonical
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Degree : PrefixCount.OrdinaryQeq1AuxDegreeMatrixGoal)
    (hQeq1Match : PrefixCount.OrdinaryQeq1SpecialMatchingGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxMatching_and_rootFlatCanonical
    hQge2Closure
    (PrefixCount.ordinaryQeq1AuxMatrixGoal_of_degreeMatrix hQeq1Degree)
    hQeq1Match hReturn

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1Margin_and_geometry
    (hQge2 : PrefixCount.MarginTransportQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1Goal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_margins_and_geometry
    (PrefixCount.marginTransportQge2Goal_of_plan hQge2)
    hQeq1 hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1Compat_and_geometry
    (hQge2 : PrefixCount.MarginTransportQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1CompatibleGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1Margin_and_geometry
    hQge2
    (PrefixCount.marginTransportQeq1Goal_of_compatible hQeq1)
    hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1MatchedPMOne_and_geometry
    (hQge2 : PrefixCount.MarginTransportQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1MatchedPMOneGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1Compat_and_geometry
    hQge2
    (PrefixCount.marginTransportQeq1CompatibleGoal_of_matchedPMOne hQeq1)
    hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1PlusFamily_and_geometry
    (hQge2 : PrefixCount.MarginTransportQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1MatchedPMOne_and_geometry
    hQge2
    (PrefixCount.marginTransportQeq1MatchedPMOneGoal_of_plusFamily hQeq1)
    hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1PlusFamily_and_rootFlatCanonical
    (hQge2 : PrefixCount.MarginTransportQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1PlusFamily_and_geometry
    hQge2 hQeq1
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)

theorem oddCoreHighModulusPrefixCountGoal_of_qge2PlanParts_qeq1PlusFamily_and_geometry
    (hQge2Plan : PrefixCount.MarginPlanQge2Goal)
    (hQge2Matrix : PrefixCount.SignedMarginMatrixForQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1PlusFamily_and_geometry
    (PrefixCount.marginTransportQge2PlanGoal_of_plan_and_matrix
      hQge2Plan hQge2Matrix)
    hQeq1 hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2PlanParts_qeq1PlusFamily_and_rootFlat
    (hQge2Plan : PrefixCount.MarginPlanQge2Goal)
    (hQge2Matrix : PrefixCount.SignedMarginMatrixForQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatReturnGoal)
    (hLift : PrefixCountRootFlatCayleyLiftGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2PlanParts_qeq1PlusFamily_and_geometry
    hQge2Plan hQge2Matrix hQeq1
    (prefixCountGeometricCriterionGoal_of_rootFlat hReturn hLift)

theorem oddCoreHighModulusPrefixCountGoal_of_qge2PlanParts_qeq1PlusFamily_and_rootFlatEquiv
    (hQge2Plan : PrefixCount.MarginPlanQge2Goal)
    (hQge2Matrix : PrefixCount.SignedMarginMatrixForQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatReturnGoal)
    (hEquiv : PrefixCountRootFlatEquivLiftGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2PlanParts_qeq1PlusFamily_and_rootFlat
    hQge2Plan hQge2Matrix hQeq1 hReturn
    (prefixCountRootFlatCayleyLiftGoal_of_equiv hEquiv)

theorem oddCoreHighModulusPrefixCountGoal_of_qge2PlanParts_qeq1PlusFamily_and_rootFlatCanonical
    (hQge2Plan : PrefixCount.MarginPlanQge2Goal)
    (hQge2Matrix : PrefixCount.SignedMarginMatrixForQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2PlanParts_qeq1PlusFamily_and_geometry
    hQge2Plan hQge2Matrix hQeq1
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)

theorem d11SmallModulusLiftFromD5Base_of_goal
    (hSmall11 : D11SmallModulusFromD5BaseGoal) :
    D11SmallModulusLiftFromD5Base StandardCayleySolved := by
  intro m hm3 hmodd hm11 h5
  exact hSmall11 hm3 hmodd hm11 h5

theorem oddCoreSmallModulusLiftOfBase_of_goal
    (hSmallLift : OddCoreSmallModulusOfBaseGoal) :
    OddCoreSmallModulusLiftOfBase StandardCayleySolved := by
  intro d m b hdodd hd13 hmodd hm3 hmd hbSolved hbRange
  exact hSmallLift hdodd hd13 hmodd hm3 hmd hbSolved hbRange

theorem oddCoreSmallModulusOfBaseGoal_of_unitPackets
    (hPacketLift : OddCoreSmallModulusOfUnitPacketsGoal) :
    OddCoreSmallModulusOfBaseGoal := by
  intro d m b hdodd hd13 hmodd hm3 hmd hbSolved hbRange
  have hpackets :=
    _root_.RoundComposite.unitCarryPackets_spec hm3 hmodd hbRange
  exact hPacketLift hdodd hd13 hmodd hm3 hmd hbSolved
    (_root_.RoundComposite.unitCarryPackets m b d)
    hpackets.1
    hpackets.2.1
    (fun packet hp => (hpackets.2.2 packet hp).1)
    (fun packet hp a ha => (hpackets.2.2 packet hp).2 a ha)

theorem d11SmallModulusFromD5BaseGoal_of_smallUnitPacketLift
    (hSmallPacket : OddCoreSmallModulusUnitPacketLiftGoal) :
    D11SmallModulusFromD5BaseGoal := by
  intro m hm3 hmodd hm11 h5
  have hrange : 2 * 5 < 11 ∧ 11 ≤ 3 * 5 := by omega
  have hpackets :=
    _root_.RoundComposite.unitCarryPackets_spec
      (b := 5) (d := 11) (m := m) hm3 hmodd hrange
  exact hSmallPacket
    (by decide : Odd 11)
    (by decide : 11 ≤ 11)
    hmodd hm3 hm11 h5
    (_root_.RoundComposite.unitCarryPackets m 5 11)
    hpackets.1
    hpackets.2.1
    (fun packet hp => (hpackets.2.2 packet hp).1)
    (fun packet hp a ha => (hpackets.2.2 packet hp).2 a ha)

theorem oddCoreSmallModulusOfBaseGoal_of_smallUnitPacketLift
    (hSmallPacket : OddCoreSmallModulusUnitPacketLiftGoal) :
    OddCoreSmallModulusOfBaseGoal := by
  intro d m b hdodd hd13 hmodd hm3 hmd hbSolved hbRange
  have hpackets :=
    _root_.RoundComposite.unitCarryPackets_spec hm3 hmodd hbRange
  exact hSmallPacket hdodd (by omega) hmodd hm3 hmd hbSolved
    (_root_.RoundComposite.unitCarryPackets m b d)
    hpackets.1
    hpackets.2.1
    (fun packet hp => (hpackets.2.2 packet hp).1)
    (fun packet hp a ha => (hpackets.2.2 packet hp).2 a ha)

theorem d11SmallModulusFromD5BaseGoal_of_slackPacketLift
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal) :
    D11SmallModulusFromD5BaseGoal := by
  intro m hm3 hmodd hm11 h5
  have hrange : 2 * 5 < 11 ∧ 11 ≤ 3 * 5 := by omega
  have hpackets :=
    _root_.RoundComposite.unitCarryPackets_spec
      (b := 5) (d := 11) (m := m) hm3 hmodd hrange
  have hTail : 11 - 5 > 5 := by omega
  have hpow4 : 66 < m ^ 4 := by
    have hmono : 3 ^ 4 ≤ m ^ 4 := Nat.pow_le_pow_left hm3 4
    norm_num at hmono ⊢
    omega
  have hSlack : m ^ 5 > m * 11 * (11 - 5) := by
    have hmpos : 0 < m := by omega
    have hmul : m * 66 < m * (m ^ 4) :=
      Nat.mul_lt_mul_of_pos_left hpow4 hmpos
    nlinarith
  exact hSmallPacket
    (by decide : Odd 11)
    (by decide : 11 ≤ 11)
    hmodd hm3 hm11 h5
    (_root_.RoundComposite.unitCarryPackets m 5 11)
    hpackets.1
    hpackets.2.1
    (fun packet hp => (hpackets.2.2 packet hp).1)
    (fun packet hp a ha => (hpackets.2.2 packet hp).2 a ha)
    hTail hSlack

theorem oddCoreSmallGE13_of_slackPacketLift
    (hBaseSlack : OddCoreSmallBaseSlackWitnessGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal) :
    OddCoreSmallGE13 StandardCayleySolved := by
  intro d m hd13 hdodd hm3 hmodd hmd
  rcases hBaseSlack hdodd hd13 hmodd hm3 hmd with
    ⟨w, hTail, hSlack⟩
  exact hSmallPacket hdodd (by omega) hmodd hm3 hmd
    (standard_cayley_odd_uniform_of_seed_semigroup w.seed hm3 hmodd)
    w.packets
    w.packets_length
    w.packets_total_length
    w.packet_sum
    w.packet_units
    hTail
    hSlack

theorem oddCoreHighGE13_of_prefix_count
    (hHigh : OddCoreHighModulusPrefixCount StandardCayleySolved) :
    OddCoreHighGE13 StandardCayleySolved := by
  intro d m hd13 hdodd hm3 hmodd hdm
  exact hHigh hdodd (by omega) hm3 hmodd hdm

theorem standard_cayley_odd_uniform_11_of_high_and_d5_base_tail
    (hHigh : OddCoreHighModulusPrefixCount StandardCayleySolved)
    (hSmall11 : D11SmallModulusLiftFromD5Base StandardCayleySolved) :
    OddUniformSolved StandardCayleySolved 11 := by
  intro m hm3 hmodd
  by_cases hm11 : 11 ≤ m
  · exact hHigh (by decide : Odd 11) (by decide : 5 ≤ 11) hm3 hmodd hm11
  · exact hSmall11 hm3 hmodd (lt_of_not_ge hm11)
      (standard_cayley_odd_uniform_5 hm3 hmodd)

theorem oddCoreSmallGE13_of_seed_semigroup_base
    (hLift : OddCoreSmallModulusLiftOfBase StandardCayleySolved) :
    OddCoreSmallGE13 StandardCayleySolved := by
  intro d m hd13 hdodd hm3 hmodd hmd
  rcases seed_semigroup_base_available hdodd hd13 with
    ⟨b, hbSeed, hbRange⟩
  exact hLift hdodd hd13 hmodd hm3 hmd
    (standard_cayley_odd_uniform_of_seed_semigroup hbSeed hm3 hmodd)
    hbRange

theorem standard_cayley_odd_uniform_9_of_3 :
    OddUniformSolved StandardCayleySolved 9 := by
  intro m hm3 hmodd
  simpa using
    (odd_uniform_cayley_mul_of_standard
      (a := 3) (b := 3) (by decide) (by decide)
      standard_cayley_odd_uniform_3 standard_cayley_odd_uniform_3
      (m := m) hm3 hmodd)

theorem odd_modulus_tori_odd_dimension_core_of_branches
    (hD11 : OddUniformSolved StandardCayleySolved 11)
    (hHigh : OddCoreHighGE13 StandardCayleySolved)
    (hSmall : OddCoreSmallGE13 StandardCayleySolved)
    {d : Nat} (hdodd : Odd d) (hd3 : 3 ≤ d) :
    OddUniformSolved StandardCayleySolved d := by
  intro m hm3 hmodd
  by_cases h3 : d = 3
  · subst d
    exact standard_cayley_odd_uniform_3 hm3 hmodd
  by_cases h5 : d = 5
  · subst d
    exact standard_cayley_odd_uniform_5 hm3 hmodd
  by_cases h7 : d = 7
  · subst d
    exact standard_cayley_odd_uniform_7 hm3 hmodd
  by_cases h9 : d = 9
  · subst d
    exact standard_cayley_odd_uniform_9_of_3 hm3 hmodd
  by_cases h11 : d = 11
  · subst d
    exact hD11 hm3 hmodd
  have hd13 : 13 ≤ d := by
    rcases hdodd with ⟨k, hk⟩
    omega
  by_cases hdm : d ≤ m
  · exact hHigh hd13 hdodd hm3 hmodd hdm
  · exact hSmall hd13 hdodd hm3 hmodd (lt_of_not_ge hdm)

theorem odd_modulus_tori_all_dimensions_of_odd_core_branches
    (hD11 : OddUniformSolved StandardCayleySolved 11)
    (hHigh : OddCoreHighGE13 StandardCayleySolved)
    (hSmall : OddCoreSmallGE13 StandardCayleySolved)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_odd_core
    (fun hd3 hdodd =>
      odd_modulus_tori_odd_dimension_core_of_branches
        hD11 hHigh hSmall hdodd hd3)
    hd2 hmodd hm3

theorem odd_modulus_tori_odd_dimension_core_of_refined_branches
    (hHigh : OddCoreHighModulusPrefixCount StandardCayleySolved)
    (hD11Small : D11SmallModulusLiftFromD5Base StandardCayleySolved)
    (hSmallLift : OddCoreSmallModulusLiftOfBase StandardCayleySolved)
    {d : Nat} (hdodd : Odd d) (hd3 : 3 ≤ d) :
    OddUniformSolved StandardCayleySolved d :=
  odd_modulus_tori_odd_dimension_core_of_branches
    (standard_cayley_odd_uniform_11_of_high_and_d5_base_tail
      hHigh hD11Small)
    (oddCoreHighGE13_of_prefix_count hHigh)
    (oddCoreSmallGE13_of_seed_semigroup_base hSmallLift)
    hdodd hd3

theorem odd_modulus_tori_all_dimensions_of_refined_branches
    (hHigh : OddCoreHighModulusPrefixCount StandardCayleySolved)
    (hD11Small : D11SmallModulusLiftFromD5Base StandardCayleySolved)
    (hSmallLift : OddCoreSmallModulusLiftOfBase StandardCayleySolved)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_odd_core
    (fun hd3 hdodd =>
      odd_modulus_tori_odd_dimension_core_of_refined_branches
        hHigh hD11Small hSmallLift hdodd hd3)
    hd2 hmodd hm3

theorem odd_modulus_tori_odd_dimension_core_of_main_lemmas
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hD11Small : D11SmallModulusFromD5BaseGoal)
    (hSmallLift : OddCoreSmallModulusOfBaseGoal)
    {d : Nat} (hdodd : Odd d) (hd3 : 3 ≤ d) :
    OddUniformSolved StandardCayleySolved d :=
  odd_modulus_tori_odd_dimension_core_of_refined_branches
    (oddCoreHighModulusPrefixCount_of_goal hHigh)
    (d11SmallModulusLiftFromD5Base_of_goal hD11Small)
    (oddCoreSmallModulusLiftOfBase_of_goal hSmallLift)
    hdodd hd3

theorem odd_modulus_tori_all_dimensions_of_main_lemmas
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hD11Small : D11SmallModulusFromD5BaseGoal)
    (hSmallLift : OddCoreSmallModulusOfBaseGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_refined_branches
    (oddCoreHighModulusPrefixCount_of_goal hHigh)
    (d11SmallModulusLiftFromD5Base_of_goal hD11Small)
    (oddCoreSmallModulusLiftOfBase_of_goal hSmallLift)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_high_and_small_packet_lift
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmallPacket : OddCoreSmallModulusUnitPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_main_lemmas
    hHigh
    (d11SmallModulusFromD5BaseGoal_of_smallUnitPacketLift hSmallPacket)
    (oddCoreSmallModulusOfBaseGoal_of_smallUnitPacketLift hSmallPacket)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_odd_core_branches
    (standard_cayley_odd_uniform_11_of_high_and_d5_base_tail
      (oddCoreHighModulusPrefixCount_of_goal hHigh)
      (d11SmallModulusLiftFromD5Base_of_goal
        (d11SmallModulusFromD5BaseGoal_of_slackPacketLift hSmallPacket)))
    (oddCoreHighGE13_of_prefix_count
      (oddCoreHighModulusPrefixCount_of_goal hHigh))
    (oddCoreSmallGE13_of_slackPacketLift
      oddCoreSmallBaseSlackWitnessGoal_of_seed_semigroup hSmallPacket)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_high_and_successor_small
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_357_and_successor
    (oddSuccessorClosureGoal_of_high_and_successorSmall hHigh hSmall)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_successor_high_and_successor_small
    (hHigh : OddSuccessorHighModulusPrefixCountGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_357_and_successor
    (oddSuccessorClosureGoal_of_successorHigh_and_successorSmall
      hHigh hSmall)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_high_and_successor_small_via_successorHigh
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_successor_high_and_successor_small
    (oddSuccessorHighModulusPrefixCountGoal_of_high hHigh)
    hSmall hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Compat_qeq1Compat_rootFlatCanonical
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1CompatibleGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_and_successor_small
    (oddCoreHighModulusPrefixCountGoal_of_qge2Compat_qeq1Compat_and_rootFlatCanonical
      hQge2 hQeq1 hReturn)
    hSmall hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Compat_qeq1Compat_rootFlatCanonical_and_slackPacketLift
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1CompatibleGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Compat_qeq1Compat_rootFlatCanonical
    hQge2 hQeq1 hReturn
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLift hSmallPacket)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_ordinarySignedCores_rootFlatCanonical_and_slackPacketLift
    (hQge2 : PrefixCount.OrdinaryQge2SignedCoreGoal)
    (hQeq1 : PrefixCount.OrdinaryQeq1SignedCoreGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Compat_qeq1Compat_rootFlatCanonical_and_slackPacketLift
    (PrefixCount.marginTransportQge2CompatibleGoal_of_ordinaryQge2SignedCore
      hQge2)
    (PrefixCount.marginTransportQeq1CompatibleGoal_of_ordinaryQeq1SignedCore
      hQeq1)
    hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_ordinarySignedCores_geometry_and_slackPacketLift
    (hQge2 : PrefixCount.OrdinaryQge2SignedCoreGoal)
    (hQeq1 : PrefixCount.OrdinaryQeq1SignedCoreGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (oddCoreHighModulusPrefixCountGoal_of_ordinarySignedCores_and_geometry
      hQge2 hQeq1 hGeom)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Core_geometry_and_slackPacketLift
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1 : PrefixCount.OrdinaryQeq1SignedCoreGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Core_and_geometry
      hQge2Matrix hQeq1 hGeom)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Core_rootFlatCanonical_and_slackPacketLift
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1 : PrefixCount.OrdinaryQeq1SignedCoreGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Core_geometry_and_slackPacketLift
    hQge2Matrix hQeq1
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Canonical_geometry_and_slackPacketLift
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1CanonicalMatrixGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Core_geometry_and_slackPacketLift
    hQge2Matrix
    (PrefixCount.ordinaryQeq1SignedCoreGoal_of_canonicalMatrix hQeq1Matrix)
    hGeom hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1Canonical_geometry_and_slackPacketLift
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1CanonicalMatrixGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Canonical_geometry_and_slackPacketLift
    (PrefixCount.ordinaryQge2SignedMatrixGoal_of_signedSeedClosure
      hQge2Closure)
    hQeq1Matrix hGeom hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Canonical_rootFlatCanonical_and_slackPacketLift
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1CanonicalMatrixGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Canonical_geometry_and_slackPacketLift
    hQge2Matrix hQeq1Matrix
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1Canonical_rootFlatCanonical_and_slackPacketLift
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1CanonicalMatrixGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1Canonical_geometry_and_slackPacketLift
    hQge2Closure hQeq1Matrix
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1Correction_rootFlatCanonical_and_slackPacketLift
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Correction : PrefixCount.OrdinaryQeq1CanonicalCorrectionGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1Canonical_rootFlatCanonical_and_slackPacketLift
    hQge2Closure
    (PrefixCount.ordinaryQeq1CanonicalMatrixGoal_of_correction
      hQeq1Correction)
    hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1CorrectionData_rootFlatCanonical_and_slackPacketLift
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Data : PrefixCount.OrdinaryQeq1CanonicalCorrectionDataGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1Correction_rootFlatCanonical_and_slackPacketLift
    hQge2Closure
    (PrefixCount.ordinaryQeq1CanonicalCorrectionGoal_of_dataGoal hQeq1Data)
    hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1AuxMatching_rootFlatCanonical_and_slackPacketLift
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Aux : PrefixCount.OrdinaryQeq1AuxMatrixGoal)
    (hQeq1Match : PrefixCount.OrdinaryQeq1SpecialMatchingGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1CorrectionData_rootFlatCanonical_and_slackPacketLift
    hQge2Closure
    (PrefixCount.ordinaryQeq1CanonicalCorrectionDataGoal_of_auxMatrix_and_specialMatching
      hQeq1Aux hQeq1Match)
    hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1AuxSpecialMatchingData_rootFlatCanonical_and_slackPacketLift
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Data : PrefixCount.OrdinaryQeq1AuxSpecialMatchingDataGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1CorrectionData_rootFlatCanonical_and_slackPacketLift
    hQge2Closure
    (PrefixCount.ordinaryQeq1CanonicalCorrectionDataGoal_of_auxSpecialMatchingData
      hQeq1Data)
    hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1AuxPRowSpecialMatchingData_rootFlatCanonical_and_slackPacketLift
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Data : PrefixCount.OrdinaryQeq1AuxPRowSpecialMatchingDataGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1AuxSpecialMatchingData_rootFlatCanonical_and_slackPacketLift
    hQge2Closure
    (PrefixCount.ordinaryQeq1AuxSpecialMatchingDataGoal_of_pRowSpecialMatchingData
      hQeq1Data)
    hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1AuxTargetHallData_rootFlatCanonical_and_slackPacketLift
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Data : PrefixCount.OrdinaryQeq1AuxTargetHallDataGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1AuxPRowSpecialMatchingData_rootFlatCanonical_and_slackPacketLift
    hQge2Closure
    (PrefixCount.ordinaryQeq1AuxPRowSpecialMatchingDataGoal_of_targetHallData
      hQeq1Data)
    hReturn hSmallPacket hd2 hmodd hm3

def OddModulusToriV4ConstructionBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1CanonicalCorrectionDataGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4JointMatchingBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1AuxSpecialMatchingDataGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4PRowMatchingBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1AuxPRowSpecialMatchingDataGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4TargetHallBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1AuxTargetHallDataGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4DegreeSpecialMatchingBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1DegreeSpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

theorem not_oddModulusToriV4DegreeSpecialMatchingBlocksGoal :
    ¬ OddModulusToriV4DegreeSpecialMatchingBlocksGoal := by
  intro hBlocks
  exact PrefixCount.not_ordinaryQeq1DegreeSpecialMatchingGoal hBlocks.2.1

def OddModulusToriV4PreferredBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4ProperCutBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4ScheduleBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  PrefixCountRootFlatCanonicalScheduleCriterionGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4ScheduleAddBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  PrefixCountRootFlatCanonicalScheduleCriterionGoal ∧
  OddCoreSmallModulusSlackPacketLiftAddGoal

def OddCoreHighModulusScheduleBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  PrefixCountRootFlatCanonicalScheduleCriterionGoal

def OddCoreHighModulusSectionMonodromyBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  PrefixCountFirstHitHeadTailSectionMonodromyGoal

def OddCoreHighModulusReturnTailMonodromyBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  PrefixCountFirstHitReturnTailMonodromyGoal

def OddCoreHighModulusReturnTailOrbitBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  PrefixCountFirstHitReturnTailMonodromyOrbitGoal

def OddCoreHighModulusReturnTailRankBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  PrefixCountFirstHitReturnTailRankGoal

def OddCoreHighModulusReturnTailRankEquivBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  PrefixCountFirstHitReturnTailRankEquivGoal

def OddCoreHighModulusReturnTailCycleCoordinateBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  PrefixCountFirstHitReturnTailCycleCoordinateGoal

def OddCoreHighModulusColumnPackingScheduleBlocksGoal : Prop :=
  PrefixCount.Qge2SignedColumnPackingGoal ∧
  PrefixCountRootFlatCanonicalScheduleCriterionGoal

theorem not_oddCoreHighModulusColumnPackingScheduleBlocksGoal :
    ¬ OddCoreHighModulusColumnPackingScheduleBlocksGoal := by
  intro hBlocks
  exact PrefixCount.not_qge2SignedColumnPackingGoal hBlocks.1

def OddModulusToriV4MinimalBlocksGoal : Prop :=
  OddCoreHighModulusScheduleBlocksGoal ∧
  OddSuccessorSmallModulusBaseTailGoal

def OddModulusToriV4SectionMonodromyBlocksGoal : Prop :=
  OddCoreHighModulusSectionMonodromyBlocksGoal ∧
  OddSuccessorSmallModulusBaseTailGoal

def OddModulusToriV4ReturnTailMonodromyBlocksGoal : Prop :=
  OddCoreHighModulusReturnTailMonodromyBlocksGoal ∧
  OddSuccessorSmallModulusBaseTailGoal

def OddModulusToriV4ReturnTailOrbitBlocksGoal : Prop :=
  OddCoreHighModulusReturnTailOrbitBlocksGoal ∧
  OddSuccessorSmallModulusBaseTailGoal

def OddModulusToriV4ReturnTailRankBlocksGoal : Prop :=
  OddCoreHighModulusReturnTailRankBlocksGoal ∧
  OddSuccessorSmallModulusBaseTailGoal

def OddModulusToriV4ReturnTailRankEquivBlocksGoal : Prop :=
  OddCoreHighModulusReturnTailRankEquivBlocksGoal ∧
  OddSuccessorSmallModulusBaseTailGoal

def OddModulusToriV4ReturnTailCycleCoordinateBlocksGoal : Prop :=
  OddCoreHighModulusReturnTailCycleCoordinateBlocksGoal ∧
  OddSuccessorSmallModulusBaseTailGoal

def OddModulusToriV4MinimalAddBlocksGoal : Prop :=
  OddCoreHighModulusScheduleBlocksGoal ∧
  OddSuccessorSmallModulusSlackPacketLiftAddGoal

def OddModulusToriV4SuccessorHighSmallBlocksGoal : Prop :=
  OddSuccessorHighModulusPrefixCountGoal ∧
  OddSuccessorSmallModulusBaseTailGoal

def OddModulusToriV4SuccessorHighSmallAddBlocksGoal : Prop :=
  OddSuccessorHighModulusPrefixCountGoal ∧
  OddSuccessorSmallModulusSlackPacketLiftAddGoal

def OddModulusToriV4ColumnPackingScheduleBlocksGoal : Prop :=
  OddCoreHighModulusColumnPackingScheduleBlocksGoal ∧
  OddSuccessorSmallModulusBaseTailGoal

def OddModulusToriV4ColumnPackingScheduleAddBlocksGoal : Prop :=
  OddCoreHighModulusColumnPackingScheduleBlocksGoal ∧
  OddSuccessorSmallModulusSlackPacketLiftAddGoal

theorem not_oddModulusToriV4ColumnPackingScheduleBlocksGoal :
    ¬ OddModulusToriV4ColumnPackingScheduleBlocksGoal := by
  intro hBlocks
  exact not_oddCoreHighModulusColumnPackingScheduleBlocksGoal hBlocks.1

theorem not_oddModulusToriV4ColumnPackingScheduleAddBlocksGoal :
    ¬ OddModulusToriV4ColumnPackingScheduleAddBlocksGoal := by
  intro hBlocks
  exact not_oddCoreHighModulusColumnPackingScheduleBlocksGoal hBlocks.1

def OddModulusToriV4SuccessorScheduleBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  PrefixCountRootFlatCanonicalScheduleCriterionGoal ∧
  OddSuccessorSmallModulusBaseTailGoal

def OddModulusToriV4SuccessorScheduleAddBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  PrefixCountRootFlatCanonicalScheduleCriterionGoal ∧
  OddSuccessorSmallModulusSlackPacketLiftAddGoal

def OddModulusToriV4DegreeMatchingBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1AuxDegreeMatrixGoal ∧
  PrefixCount.OrdinaryQeq1SpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4UniformDegreeBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1AuxDegreeArithmeticGoal ∧
  PrefixCount.UniformColumnDegreeMatrixGoal ∧
  PrefixCount.OrdinaryQeq1SpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4UniformTotalBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1AuxDegreeTotalGoal ∧
  PrefixCount.UniformColumnDegreeMatrixGoal ∧
  PrefixCount.OrdinaryQeq1SpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4PostTotalBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.UniformColumnDegreeMatrixGoal ∧
  PrefixCount.OrdinaryQeq1SpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4ResidueBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.UniformColumnDegreeResidueCountGoal ∧
  PrefixCount.OrdinaryQeq1SpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4IntervalBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.UniformColumnDegreeIntervalPartitionGoal ∧
  PrefixCount.OrdinaryQeq1SpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4PostUniformBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1SpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

theorem odd_modulus_tori_all_dimensions_of_v4_construction_blocks
    (hBlocks : OddModulusToriV4ConstructionBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with ⟨hQge2Closure, hQeq1Data, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1CorrectionData_rootFlatCanonical_and_slackPacketLift
      hQge2Closure hQeq1Data hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_joint_matching_blocks
    (hBlocks : OddModulusToriV4JointMatchingBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with ⟨hQge2Closure, hQeq1Data, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1AuxSpecialMatchingData_rootFlatCanonical_and_slackPacketLift
      hQge2Closure hQeq1Data hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_pRow_matching_blocks
    (hBlocks : OddModulusToriV4PRowMatchingBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with ⟨hQge2Closure, hQeq1Data, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1AuxPRowSpecialMatchingData_rootFlatCanonical_and_slackPacketLift
      hQge2Closure hQeq1Data hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_targetHall_blocks
    (hBlocks : OddModulusToriV4TargetHallBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with ⟨hQge2Closure, hQeq1Data, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1AuxTargetHallData_rootFlatCanonical_and_slackPacketLift
      hQge2Closure hQeq1Data hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_degree_special_matching_blocks
    (hBlocks : OddModulusToriV4DegreeSpecialMatchingBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with ⟨hQge2Closure, hQeq1Match, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1AuxSpecialMatchingData_rootFlatCanonical_and_slackPacketLift
      hQge2Closure
      (PrefixCount.ordinaryQeq1AuxSpecialMatchingDataGoal_of_degreeSpecialMatching
        hQeq1Match)
      hReturn hSmallPacket hd2 hmodd hm3

theorem oddCoreHighModulusPrefixCountGoal_of_v4_preferred_blocks
    (hBlocks : OddModulusToriV4PreferredBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal := by
  rcases hBlocks with ⟨hQge2Closure, hReturn, _hSmallPacket⟩
  exact
    oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxTargetHallData_and_rootFlatCanonical
      hQge2Closure PrefixCount.ordinaryQeq1AuxTargetHallDataGoal hReturn

theorem odd_successor_small_modulus_base_tail_of_v4_preferred_blocks
    (hBlocks : OddModulusToriV4PreferredBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hmSmall : m < 2 * b + 1)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m := by
  rcases hBlocks with ⟨_hQge2Closure, _hReturn, hSmallPacket⟩
  exact odd_successor_small_modulus_base_tail_of_slackPacketLift
    hSmallPacket hb5 hmodd hm3 hmSmall hb

theorem oddSuccessorClosureGoal_of_v4_preferred_blocks
    (hBlocks : OddModulusToriV4PreferredBlocksGoal) :
    OddSuccessorClosureGoal := by
  rcases hBlocks with ⟨hQge2Closure, hReturn, hSmallPacket⟩
  exact oddSuccessorClosureGoal_of_high_and_slackPacketLift
    (oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxTargetHallData_and_rootFlatCanonical
      hQge2Closure PrefixCount.ordinaryQeq1AuxTargetHallDataGoal hReturn)
    hSmallPacket

theorem odd_successor_closure_of_v4_preferred_blocks
    (hBlocks : OddModulusToriV4PreferredBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_v4_preferred_blocks hBlocks)
    hb5 hmodd hm3 hb

theorem odd_modulus_tori_all_dimensions_of_v4_preferred_blocks
    (hBlocks : OddModulusToriV4PreferredBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  let targetHallBlocks : OddModulusToriV4TargetHallBlocksGoal :=
    ⟨hBlocks.1, PrefixCount.ordinaryQeq1AuxTargetHallDataGoal,
      hBlocks.2.1, hBlocks.2.2⟩
  odd_modulus_tori_all_dimensions_of_v4_targetHall_blocks
    targetHallBlocks hd2 hmodd hm3

theorem oddModulusToriV4PreferredBlocksGoal_of_properCutBlocks
    (hBlocks : OddModulusToriV4ProperCutBlocksGoal) :
    OddModulusToriV4PreferredBlocksGoal :=
  ⟨PrefixCount.ordinaryQge2SignedSeedClosureGoal_of_properCutClosure
      hBlocks.1,
    hBlocks.2.1, hBlocks.2.2⟩

theorem oddModulusToriV4ProperCutBlocksGoal_of_scheduleBlocks
    (hBlocks : OddModulusToriV4ScheduleBlocksGoal) :
    OddModulusToriV4ProperCutBlocksGoal :=
  ⟨hBlocks.1,
    prefixCountRootFlatCanonicalReturnGoal_of_scheduleCriterion hBlocks.2.1,
    hBlocks.2.2⟩

theorem oddModulusToriV4PreferredBlocksGoal_of_scheduleBlocks
    (hBlocks : OddModulusToriV4ScheduleBlocksGoal) :
    OddModulusToriV4PreferredBlocksGoal :=
  oddModulusToriV4PreferredBlocksGoal_of_properCutBlocks
    (oddModulusToriV4ProperCutBlocksGoal_of_scheduleBlocks hBlocks)

theorem oddModulusToriV4ScheduleBlocksGoal_of_scheduleAddBlocks
    (hBlocks : OddModulusToriV4ScheduleAddBlocksGoal) :
    OddModulusToriV4ScheduleBlocksGoal :=
  ⟨hBlocks.1, hBlocks.2.1,
    oddCoreSmallModulusSlackPacketLiftGoal_of_add hBlocks.2.2⟩

theorem oddModulusToriV4ProperCutBlocksGoal_of_scheduleAddBlocks
    (hBlocks : OddModulusToriV4ScheduleAddBlocksGoal) :
    OddModulusToriV4ProperCutBlocksGoal :=
  oddModulusToriV4ProperCutBlocksGoal_of_scheduleBlocks
    (oddModulusToriV4ScheduleBlocksGoal_of_scheduleAddBlocks hBlocks)

theorem oddModulusToriV4PreferredBlocksGoal_of_scheduleAddBlocks
    (hBlocks : OddModulusToriV4ScheduleAddBlocksGoal) :
    OddModulusToriV4PreferredBlocksGoal :=
  oddModulusToriV4PreferredBlocksGoal_of_scheduleBlocks
    (oddModulusToriV4ScheduleBlocksGoal_of_scheduleAddBlocks hBlocks)

theorem oddModulusToriV4SuccessorScheduleAddBlocksGoal_of_scheduleAddBlocks
    (hBlocks : OddModulusToriV4ScheduleAddBlocksGoal) :
    OddModulusToriV4SuccessorScheduleAddBlocksGoal :=
  ⟨hBlocks.1, hBlocks.2.1,
    oddSuccessorSmallModulusSlackPacketLiftAddGoal_of_coreAdd hBlocks.2.2⟩

theorem oddModulusToriV4SuccessorScheduleBlocksGoal_of_successorScheduleAddBlocks
    (hBlocks : OddModulusToriV4SuccessorScheduleAddBlocksGoal) :
    OddModulusToriV4SuccessorScheduleBlocksGoal :=
  ⟨hBlocks.1, hBlocks.2.1,
    oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hBlocks.2.2⟩

theorem oddModulusToriV4SuccessorScheduleBlocksGoal_of_scheduleAddBlocks
    (hBlocks : OddModulusToriV4ScheduleAddBlocksGoal) :
    OddModulusToriV4SuccessorScheduleBlocksGoal :=
  oddModulusToriV4SuccessorScheduleBlocksGoal_of_successorScheduleAddBlocks
    (oddModulusToriV4SuccessorScheduleAddBlocksGoal_of_scheduleAddBlocks hBlocks)

theorem oddModulusToriV4SuccessorScheduleBlocksGoal_of_minimalBlocks
    (hBlocks : OddModulusToriV4MinimalBlocksGoal) :
    OddModulusToriV4SuccessorScheduleBlocksGoal :=
  ⟨hBlocks.1.1, hBlocks.1.2, hBlocks.2⟩

theorem oddModulusToriV4MinimalBlocksGoal_of_successorScheduleBlocks
    (hBlocks : OddModulusToriV4SuccessorScheduleBlocksGoal) :
    OddModulusToriV4MinimalBlocksGoal :=
  ⟨⟨hBlocks.1, hBlocks.2.1⟩, hBlocks.2.2⟩

theorem oddModulusToriV4MinimalBlocksGoal_iff_successorScheduleBlocks :
    OddModulusToriV4MinimalBlocksGoal ↔
      OddModulusToriV4SuccessorScheduleBlocksGoal :=
  ⟨oddModulusToriV4SuccessorScheduleBlocksGoal_of_minimalBlocks,
    oddModulusToriV4MinimalBlocksGoal_of_successorScheduleBlocks⟩

theorem oddModulusToriV4SuccessorScheduleAddBlocksGoal_of_minimalAddBlocks
    (hBlocks : OddModulusToriV4MinimalAddBlocksGoal) :
    OddModulusToriV4SuccessorScheduleAddBlocksGoal :=
  ⟨hBlocks.1.1, hBlocks.1.2, hBlocks.2⟩

theorem oddModulusToriV4MinimalAddBlocksGoal_of_successorScheduleAddBlocks
    (hBlocks : OddModulusToriV4SuccessorScheduleAddBlocksGoal) :
    OddModulusToriV4MinimalAddBlocksGoal :=
  ⟨⟨hBlocks.1, hBlocks.2.1⟩, hBlocks.2.2⟩

theorem oddModulusToriV4MinimalAddBlocksGoal_iff_successorScheduleAddBlocks :
    OddModulusToriV4MinimalAddBlocksGoal ↔
      OddModulusToriV4SuccessorScheduleAddBlocksGoal :=
  ⟨oddModulusToriV4SuccessorScheduleAddBlocksGoal_of_minimalAddBlocks,
    oddModulusToriV4MinimalAddBlocksGoal_of_successorScheduleAddBlocks⟩

theorem oddSuccessorClosureGoal_of_v4_properCut_blocks
    (hBlocks : OddModulusToriV4ProperCutBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_preferred_blocks
    (oddModulusToriV4PreferredBlocksGoal_of_properCutBlocks hBlocks)

theorem oddSuccessorClosureGoal_of_v4_schedule_blocks
    (hBlocks : OddModulusToriV4ScheduleBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_properCut_blocks
    (oddModulusToriV4ProperCutBlocksGoal_of_scheduleBlocks hBlocks)

theorem oddSuccessorClosureGoal_of_v4_scheduleAdd_blocks
    (hBlocks : OddModulusToriV4ScheduleAddBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_schedule_blocks
    (oddModulusToriV4ScheduleBlocksGoal_of_scheduleAddBlocks hBlocks)

theorem odd_successor_closure_of_v4_properCut_blocks
    (hBlocks : OddModulusToriV4ProperCutBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_v4_properCut_blocks hBlocks)
    hb5 hmodd hm3 hb

theorem odd_successor_closure_of_v4_schedule_blocks
    (hBlocks : OddModulusToriV4ScheduleBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_v4_schedule_blocks hBlocks)
    hb5 hmodd hm3 hb

theorem odd_successor_closure_of_v4_scheduleAdd_blocks
    (hBlocks : OddModulusToriV4ScheduleAddBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_v4_scheduleAdd_blocks hBlocks)
    hb5 hmodd hm3 hb

theorem odd_modulus_tori_all_dimensions_of_v4_properCut_blocks
    (hBlocks : OddModulusToriV4ProperCutBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_preferred_blocks
    (oddModulusToriV4PreferredBlocksGoal_of_properCutBlocks hBlocks)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_schedule_blocks
    (hBlocks : OddModulusToriV4ScheduleBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_properCut_blocks
    (oddModulusToriV4ProperCutBlocksGoal_of_scheduleBlocks hBlocks)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_scheduleAdd_blocks
    (hBlocks : OddModulusToriV4ScheduleAddBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_schedule_blocks
    (oddModulusToriV4ScheduleBlocksGoal_of_scheduleAddBlocks hBlocks)
    hd2 hmodd hm3

theorem oddCoreHighModulusPrefixCountGoal_of_v4_properCut_blocks
    (hBlocks : OddModulusToriV4ProperCutBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_preferred_blocks
    (oddModulusToriV4PreferredBlocksGoal_of_properCutBlocks hBlocks)

theorem oddCoreHighModulusPrefixCountGoal_of_v4_schedule_blocks
    (hBlocks : OddModulusToriV4ScheduleBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_properCut_blocks
    (oddModulusToriV4ProperCutBlocksGoal_of_scheduleBlocks hBlocks)

theorem oddCoreHighModulusPrefixCountGoal_of_v4_scheduleAdd_blocks
    (hBlocks : OddModulusToriV4ScheduleAddBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_schedule_blocks
    (oddModulusToriV4ScheduleBlocksGoal_of_scheduleAddBlocks hBlocks)

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highSchedule_blocks
    (hBlocks : OddCoreHighModulusScheduleBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxTargetHallData_and_rootFlatCanonical
    (PrefixCount.ordinaryQge2SignedSeedClosureGoal_of_properCutClosure hBlocks.1)
    PrefixCount.ordinaryQeq1AuxTargetHallDataGoal
    (prefixCountRootFlatCanonicalReturnGoal_of_scheduleCriterion hBlocks.2)

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highSchedule
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highSchedule_blocks
    ⟨hQge2Proper, hSchedule⟩

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highSectionMonodromy_blocks
    (hBlocks : OddCoreHighModulusSectionMonodromyBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highSchedule
    hBlocks.1
    (prefixCountRootFlatCanonicalScheduleCriterionGoal_of_sectionMonodromy
      hBlocks.2)

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highSectionMonodromy
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hSection : PrefixCountFirstHitHeadTailSectionMonodromyGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highSectionMonodromy_blocks
    ⟨hQge2Proper, hSection⟩

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailMonodromy_blocks
    (hBlocks : OddCoreHighModulusReturnTailMonodromyBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highSectionMonodromy
    hBlocks.1
    (prefixCountFirstHitHeadTailSectionMonodromyGoal_of_returnTailMonodromy
      hBlocks.2)

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailMonodromy
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hTail : PrefixCountFirstHitReturnTailMonodromyGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailMonodromy_blocks
    ⟨hQge2Proper, hTail⟩

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailOrbit_blocks
    (hBlocks : OddCoreHighModulusReturnTailOrbitBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailMonodromy
    hBlocks.1
    (prefixCountFirstHitReturnTailMonodromyGoal_of_orbit hBlocks.2)

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailOrbit
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailOrbit_blocks
    ⟨hQge2Proper, hOrbit⟩

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailRank_blocks
    (hBlocks : OddCoreHighModulusReturnTailRankBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailOrbit
    hBlocks.1
    (prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_rank hBlocks.2)

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailRank
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hRank : PrefixCountFirstHitReturnTailRankGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailRank_blocks
    ⟨hQge2Proper, hRank⟩

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailRankEquiv_blocks
    (hBlocks : OddCoreHighModulusReturnTailRankEquivBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailRank
    hBlocks.1
    (prefixCountFirstHitReturnTailRankGoal_of_rankEquiv hBlocks.2)

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailRankEquiv
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hEquiv : PrefixCountFirstHitReturnTailRankEquivGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailRankEquiv_blocks
    ⟨hQge2Proper, hEquiv⟩

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailCycleCoordinate_blocks
    (hBlocks : OddCoreHighModulusReturnTailCycleCoordinateBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailRankEquiv
    hBlocks.1
    (prefixCountFirstHitReturnTailRankEquivGoal_of_cycleCoordinate hBlocks.2)

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailCycleCoordinate
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hCycle : PrefixCountFirstHitReturnTailCycleCoordinateGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailCycleCoordinate_blocks
    ⟨hQge2Proper, hCycle⟩

theorem oddCoreHighModulusPrefixCountGoal_of_v4_columnPackingSchedule
    (hPacking : PrefixCount.Qge2SignedColumnPackingGoal)
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highSchedule
    (PrefixCount.ordinaryQge2SignedSeedProperCutClosureGoal_of_signedSeedClosure
      (PrefixCount.ordinaryQge2SignedSeedClosureGoal_of_columnPacking
        hPacking))
    hSchedule

theorem oddCoreHighModulusPrefixCountGoal_of_v4_columnPackingSchedule_blocks
    (hBlocks : OddCoreHighModulusColumnPackingScheduleBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_columnPackingSchedule
    hBlocks.1 hBlocks.2

theorem oddCoreHighModulusPrefixCountGoal_of_v4_successorSchedule_blocks
    (hBlocks : OddModulusToriV4SuccessorScheduleBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highSchedule_blocks
    ⟨hBlocks.1, hBlocks.2.1⟩

theorem oddCoreHighModulusPrefixCountGoal_of_v4_successorScheduleAdd_blocks
    (hBlocks : OddModulusToriV4SuccessorScheduleAddBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_successorSchedule_blocks
    (oddModulusToriV4SuccessorScheduleBlocksGoal_of_successorScheduleAddBlocks
      hBlocks)

theorem oddSuccessorClosureGoal_of_v4_successorSchedule_blocks
    (hBlocks : OddModulusToriV4SuccessorScheduleBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_successorSchedule_blocks hBlocks)
    hBlocks.2.2

theorem oddSuccessorClosureGoal_of_v4_successorScheduleAdd_blocks
    (hBlocks : OddModulusToriV4SuccessorScheduleAddBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_successorSchedule_blocks
    (oddModulusToriV4SuccessorScheduleBlocksGoal_of_successorScheduleAddBlocks
      hBlocks)

theorem oddSuccessorClosureGoal_of_successorHighSmall_blocks
    (hBlocks : OddModulusToriV4SuccessorHighSmallBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_successorHigh_and_successorSmall
    hBlocks.1 hBlocks.2

theorem oddSuccessorClosureGoal_of_successorHighSmallAdd_blocks
    (hBlocks : OddModulusToriV4SuccessorHighSmallAddBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_successorHighSmall_blocks
    ⟨hBlocks.1,
      oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd
        hBlocks.2⟩

theorem oddSuccessorClosureGoal_of_v4_minimal_blocks
    (hBlocks : OddModulusToriV4MinimalBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_successorSchedule_blocks
    (oddModulusToriV4SuccessorScheduleBlocksGoal_of_minimalBlocks hBlocks)

theorem oddSuccessorClosureGoal_of_v4_sectionMonodromy_blocks
    (hBlocks : OddModulusToriV4SectionMonodromyBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_highSectionMonodromy_blocks
      hBlocks.1)
    hBlocks.2

theorem oddSuccessorClosureGoal_of_v4_returnTailMonodromy_blocks
    (hBlocks : OddModulusToriV4ReturnTailMonodromyBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailMonodromy_blocks
      hBlocks.1)
    hBlocks.2

theorem oddSuccessorClosureGoal_of_v4_returnTailOrbit_blocks
    (hBlocks : OddModulusToriV4ReturnTailOrbitBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailOrbit_blocks
      hBlocks.1)
    hBlocks.2

theorem oddSuccessorClosureGoal_of_v4_returnTailRank_blocks
    (hBlocks : OddModulusToriV4ReturnTailRankBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailRank_blocks
      hBlocks.1)
    hBlocks.2

theorem oddSuccessorClosureGoal_of_v4_returnTailRankEquiv_blocks
    (hBlocks : OddModulusToriV4ReturnTailRankEquivBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailRankEquiv_blocks
      hBlocks.1)
    hBlocks.2

theorem oddSuccessorClosureGoal_of_v4_returnTailCycleCoordinate_blocks
    (hBlocks : OddModulusToriV4ReturnTailCycleCoordinateBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailCycleCoordinate_blocks
      hBlocks.1)
    hBlocks.2

theorem oddSuccessorClosureGoal_of_v4_minimalAdd_blocks
    (hBlocks : OddModulusToriV4MinimalAddBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_successorScheduleAdd_blocks
    (oddModulusToriV4SuccessorScheduleAddBlocksGoal_of_minimalAddBlocks
      hBlocks)

theorem oddSuccessorClosureGoal_of_v4_successorSchedule
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_highSchedule
      hQge2Proper hSchedule)
    hSmall

theorem oddSuccessorClosureGoal_of_v4_sectionMonodromy
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hSection : PrefixCountFirstHitHeadTailSectionMonodromyGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_highSectionMonodromy
      hQge2Proper hSection)
    hSmall

theorem oddSuccessorClosureGoal_of_v4_returnTailMonodromy
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hTail : PrefixCountFirstHitReturnTailMonodromyGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailMonodromy
      hQge2Proper hTail)
    hSmall

theorem oddSuccessorClosureGoal_of_v4_returnTailOrbit
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailOrbit
      hQge2Proper hOrbit)
    hSmall

theorem oddSuccessorClosureGoal_of_v4_returnTailOrbitAdd
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_returnTailOrbit hQge2Proper hOrbit
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmall)

theorem oddSuccessorClosureGoal_of_v4_returnTailRank
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hRank : PrefixCountFirstHitReturnTailRankGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailRank
      hQge2Proper hRank)
    hSmall

theorem oddSuccessorClosureGoal_of_v4_returnTailRankEquiv
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hEquiv : PrefixCountFirstHitReturnTailRankEquivGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailRankEquiv
      hQge2Proper hEquiv)
    hSmall

theorem oddSuccessorClosureGoal_of_v4_returnTailCycleCoordinate
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hCycle : PrefixCountFirstHitReturnTailCycleCoordinateGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailCycleCoordinate
      hQge2Proper hCycle)
    hSmall

theorem oddSuccessorClosureGoal_of_v4_returnTailCycleCoordinateAdd
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hCycle : PrefixCountFirstHitReturnTailCycleCoordinateGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_returnTailCycleCoordinate hQge2Proper hCycle
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmall)

theorem oddSuccessorClosureGoal_of_v4_successorScheduleAdd
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_slackPacketLiftAdd
    (oddCoreHighModulusPrefixCountGoal_of_v4_highSchedule
      hQge2Proper hSchedule)
    hSmall

theorem oddSuccessorClosureGoal_of_v4_columnPackingSchedule
    (hPacking : PrefixCount.Qge2SignedColumnPackingGoal)
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_columnPackingSchedule
      hPacking hSchedule)
    hSmall

theorem oddSuccessorClosureGoal_of_v4_columnPackingScheduleAdd
    (hPacking : PrefixCount.Qge2SignedColumnPackingGoal)
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_slackPacketLiftAdd
    (oddCoreHighModulusPrefixCountGoal_of_v4_columnPackingSchedule
      hPacking hSchedule)
    hSmall

theorem oddSuccessorClosureGoal_of_v4_columnPackingSchedule_blocks
    (hBlocks : OddModulusToriV4ColumnPackingScheduleBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_columnPackingSchedule
    hBlocks.1.1 hBlocks.1.2 hBlocks.2

theorem oddSuccessorClosureGoal_of_v4_columnPackingScheduleAdd_blocks
    (hBlocks : OddModulusToriV4ColumnPackingScheduleAddBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_columnPackingScheduleAdd
    hBlocks.1.1 hBlocks.1.2 hBlocks.2

theorem odd_successor_closure_of_v4_successorSchedule_blocks
    (hBlocks : OddModulusToriV4SuccessorScheduleBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_v4_successorSchedule_blocks hBlocks)
    hb5 hmodd hm3 hb

theorem odd_successor_closure_of_v4_successorScheduleAdd_blocks
    (hBlocks : OddModulusToriV4SuccessorScheduleAddBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_v4_successorScheduleAdd_blocks hBlocks)
    hb5 hmodd hm3 hb

theorem odd_successor_closure_of_v4_minimal_blocks
    (hBlocks : OddModulusToriV4MinimalBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_v4_minimal_blocks hBlocks)
    hb5 hmodd hm3 hb

theorem odd_successor_closure_of_v4_minimalAdd_blocks
    (hBlocks : OddModulusToriV4MinimalAddBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_v4_minimalAdd_blocks hBlocks)
    hb5 hmodd hm3 hb

theorem odd_successor_closure_of_v4_successorSchedule
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_v4_successorSchedule
    hQge2Proper hSchedule hSmall)
    hb5 hmodd hm3 hb

theorem odd_successor_closure_of_v4_successorScheduleAdd
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_v4_successorScheduleAdd
    hQge2Proper hSchedule hSmall)
    hb5 hmodd hm3 hb

theorem odd_successor_closure_of_v4_columnPackingSchedule
    (hPacking : PrefixCount.Qge2SignedColumnPackingGoal)
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_v4_columnPackingSchedule
    hPacking hSchedule hSmall)
    hb5 hmodd hm3 hb

theorem odd_successor_closure_of_v4_columnPackingScheduleAdd
    (hPacking : PrefixCount.Qge2SignedColumnPackingGoal)
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_v4_columnPackingScheduleAdd
    hPacking hSchedule hSmall)
    hb5 hmodd hm3 hb

theorem odd_successor_closure_of_v4_columnPackingSchedule_blocks
    (hBlocks : OddModulusToriV4ColumnPackingScheduleBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_v4_columnPackingSchedule_blocks hBlocks)
    hb5 hmodd hm3 hb

theorem odd_successor_closure_of_v4_columnPackingScheduleAdd_blocks
    (hBlocks : OddModulusToriV4ColumnPackingScheduleAddBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_v4_columnPackingScheduleAdd_blocks hBlocks)
    hb5 hmodd hm3 hb

theorem odd_modulus_tori_all_dimensions_of_v4_successorSchedule_blocks
    (hBlocks : OddModulusToriV4SuccessorScheduleBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_and_successor_small
    (oddCoreHighModulusPrefixCountGoal_of_v4_successorSchedule_blocks hBlocks)
    hBlocks.2.2
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_successorScheduleAdd_blocks
    (hBlocks : OddModulusToriV4SuccessorScheduleAddBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_successorSchedule_blocks
    (oddModulusToriV4SuccessorScheduleBlocksGoal_of_successorScheduleAddBlocks
      hBlocks)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_successorHighSmall_blocks
    (hBlocks : OddModulusToriV4SuccessorHighSmallBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_successor_high_and_successor_small
    hBlocks.1 hBlocks.2 hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_successorHighSmallAdd_blocks
    (hBlocks : OddModulusToriV4SuccessorHighSmallAddBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_successorHighSmall_blocks
    ⟨hBlocks.1,
      oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd
        hBlocks.2⟩
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_minimal_blocks
    (hBlocks : OddModulusToriV4MinimalBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_successorSchedule_blocks
    (oddModulusToriV4SuccessorScheduleBlocksGoal_of_minimalBlocks hBlocks)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_sectionMonodromy_blocks
    (hBlocks : OddModulusToriV4SectionMonodromyBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_and_successor_small
    (oddCoreHighModulusPrefixCountGoal_of_v4_highSectionMonodromy_blocks
      hBlocks.1)
    hBlocks.2
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_sectionMonodromy
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hSection : PrefixCountFirstHitHeadTailSectionMonodromyGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_sectionMonodromy_blocks
    ⟨⟨hQge2Proper, hSection⟩, hSmall⟩
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailMonodromy_blocks
    (hBlocks : OddModulusToriV4ReturnTailMonodromyBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_and_successor_small
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailMonodromy_blocks
      hBlocks.1)
    hBlocks.2
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailMonodromy
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hTail : PrefixCountFirstHitReturnTailMonodromyGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailMonodromy_blocks
    ⟨⟨hQge2Proper, hTail⟩, hSmall⟩
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailOrbit_blocks
    (hBlocks : OddModulusToriV4ReturnTailOrbitBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_and_successor_small
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailOrbit_blocks
      hBlocks.1)
    hBlocks.2
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailOrbit
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailOrbit_blocks
    ⟨⟨hQge2Proper, hOrbit⟩, hSmall⟩
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailOrbitAdd
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailOrbit
    hQge2Proper hOrbit
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmall)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailRank_blocks
    (hBlocks : OddModulusToriV4ReturnTailRankBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_and_successor_small
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailRank_blocks
      hBlocks.1)
    hBlocks.2
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailRank
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hRank : PrefixCountFirstHitReturnTailRankGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailRank_blocks
    ⟨⟨hQge2Proper, hRank⟩, hSmall⟩
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailRankEquiv_blocks
    (hBlocks : OddModulusToriV4ReturnTailRankEquivBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_and_successor_small
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailRankEquiv_blocks
      hBlocks.1)
    hBlocks.2
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailRankEquiv
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hEquiv : PrefixCountFirstHitReturnTailRankEquivGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailRankEquiv_blocks
    ⟨⟨hQge2Proper, hEquiv⟩, hSmall⟩
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailCycleCoordinate_blocks
    (hBlocks : OddModulusToriV4ReturnTailCycleCoordinateBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_and_successor_small
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailCycleCoordinate_blocks
      hBlocks.1)
    hBlocks.2
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailCycleCoordinate
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hCycle : PrefixCountFirstHitReturnTailCycleCoordinateGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailCycleCoordinate_blocks
    ⟨⟨hQge2Proper, hCycle⟩, hSmall⟩
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailCycleCoordinateAdd
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hCycle : PrefixCountFirstHitReturnTailCycleCoordinateGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailCycleCoordinate
    hQge2Proper hCycle
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmall)
    hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_sectionMonodromy_blocks
    (hBlocks : OddModulusToriV4SectionMonodromyBlocksGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_sectionMonodromy_blocks
    hBlocks hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_sectionMonodromy
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hSection : PrefixCountFirstHitHeadTailSectionMonodromyGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_sectionMonodromy
    hQge2Proper hSection hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailMonodromy_blocks
    (hBlocks : OddModulusToriV4ReturnTailMonodromyBlocksGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailMonodromy_blocks
    hBlocks hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailMonodromy
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hTail : PrefixCountFirstHitReturnTailMonodromyGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailMonodromy
    hQge2Proper hTail hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailOrbit_blocks
    (hBlocks : OddModulusToriV4ReturnTailOrbitBlocksGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailOrbit_blocks
    hBlocks hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailOrbit
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailOrbit
    hQge2Proper hOrbit hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailOrbitAdd
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailOrbitAdd
    hQge2Proper hOrbit hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailRank_blocks
    (hBlocks : OddModulusToriV4ReturnTailRankBlocksGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailRank_blocks
    hBlocks hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailRank
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hRank : PrefixCountFirstHitReturnTailRankGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailRank
    hQge2Proper hRank hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailRankEquiv_blocks
    (hBlocks : OddModulusToriV4ReturnTailRankEquivBlocksGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailRankEquiv_blocks
    hBlocks hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailRankEquiv
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hEquiv : PrefixCountFirstHitReturnTailRankEquivGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailRankEquiv
    hQge2Proper hEquiv hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailCycleCoordinate_blocks
    (hBlocks : OddModulusToriV4ReturnTailCycleCoordinateBlocksGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailCycleCoordinate_blocks
    hBlocks hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailCycleCoordinate
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hCycle : PrefixCountFirstHitReturnTailCycleCoordinateGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailCycleCoordinate
    hQge2Proper hCycle hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailCycleCoordinateAdd
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hCycle : PrefixCountFirstHitReturnTailCycleCoordinateGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailCycleCoordinateAdd
    hQge2Proper hCycle hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_minimal_blocks
    (hBlocks : OddModulusToriV4MinimalBlocksGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_minimal_blocks
    hBlocks hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_minimalAdd_blocks
    (hBlocks : OddModulusToriV4MinimalAddBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_successorScheduleAdd_blocks
    (oddModulusToriV4SuccessorScheduleAddBlocksGoal_of_minimalAddBlocks
      hBlocks)
    hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_minimalAdd_blocks
    (hBlocks : OddModulusToriV4MinimalAddBlocksGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_minimalAdd_blocks
    hBlocks hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_successorHighSmall_blocks
    (hBlocks : OddModulusToriV4SuccessorHighSmallBlocksGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_successorHighSmall_blocks
    hBlocks hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_successorHighSmallAdd_blocks
    (hBlocks : OddModulusToriV4SuccessorHighSmallAddBlocksGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_successorHighSmallAdd_blocks
    hBlocks hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_successorSchedule
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_successorSchedule_blocks
    ⟨hQge2Proper, hSchedule, hSmall⟩
    hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_successorSchedule
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_successorSchedule
    hQge2Proper hSchedule hSmall hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_successorScheduleAdd
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_successorScheduleAdd_blocks
    ⟨hQge2Proper, hSchedule, hSmall⟩
    hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_successorScheduleAdd
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_successorScheduleAdd
    hQge2Proper hSchedule hSmall hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_columnPackingSchedule
    (hPacking : PrefixCount.Qge2SignedColumnPackingGoal)
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_successorSchedule
    (PrefixCount.ordinaryQge2SignedSeedProperCutClosureGoal_of_signedSeedClosure
      (PrefixCount.ordinaryQge2SignedSeedClosureGoal_of_columnPacking
        hPacking))
    hSchedule hSmall hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_columnPackingScheduleAdd
    (hPacking : PrefixCount.Qge2SignedColumnPackingGoal)
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_successorScheduleAdd
    (PrefixCount.ordinaryQge2SignedSeedProperCutClosureGoal_of_signedSeedClosure
      (PrefixCount.ordinaryQge2SignedSeedClosureGoal_of_columnPacking
        hPacking))
    hSchedule hSmall hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_columnPackingSchedule_blocks
    (hBlocks : OddModulusToriV4ColumnPackingScheduleBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_columnPackingSchedule
    hBlocks.1.1 hBlocks.1.2 hBlocks.2 hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_columnPackingSchedule_blocks
    (hBlocks : OddModulusToriV4ColumnPackingScheduleBlocksGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_columnPackingSchedule_blocks
    hBlocks hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_columnPackingScheduleAdd_blocks
    (hBlocks : OddModulusToriV4ColumnPackingScheduleAddBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_columnPackingScheduleAdd
    hBlocks.1.1 hBlocks.1.2 hBlocks.2 hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_columnPackingScheduleAdd_blocks
    (hBlocks : OddModulusToriV4ColumnPackingScheduleAddBlocksGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_columnPackingScheduleAdd_blocks
    hBlocks hd2 hmodd hm3

theorem odd_successor_small_modulus_base_tail_of_v4_properCut_blocks
    (hBlocks : OddModulusToriV4ProperCutBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hmSmall : m < 2 * b + 1)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  odd_successor_small_modulus_base_tail_of_v4_preferred_blocks
    (oddModulusToriV4PreferredBlocksGoal_of_properCutBlocks hBlocks)
    hb5 hmodd hm3 hmSmall hb

theorem odd_successor_small_modulus_base_tail_of_v4_schedule_blocks
    (hBlocks : OddModulusToriV4ScheduleBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hmSmall : m < 2 * b + 1)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  odd_successor_small_modulus_base_tail_of_v4_properCut_blocks
    (oddModulusToriV4ProperCutBlocksGoal_of_scheduleBlocks hBlocks)
    hb5 hmodd hm3 hmSmall hb

theorem odd_successor_small_modulus_base_tail_of_v4_scheduleAdd_blocks
    (hBlocks : OddModulusToriV4ScheduleAddBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hmSmall : m < 2 * b + 1)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  odd_successor_small_modulus_base_tail_of_v4_schedule_blocks
    (oddModulusToriV4ScheduleBlocksGoal_of_scheduleAddBlocks hBlocks)
    hb5 hmodd hm3 hmSmall hb

theorem odd_successor_small_modulus_base_tail_of_v4_successorSchedule_blocks
    (hBlocks : OddModulusToriV4SuccessorScheduleBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hmSmall : m < 2 * b + 1)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  hBlocks.2.2 hb5 hmodd hm3 hmSmall hb

theorem odd_successor_small_modulus_base_tail_of_v4_successorScheduleAdd_blocks
    (hBlocks : OddModulusToriV4SuccessorScheduleAddBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hmSmall : m < 2 * b + 1)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  odd_successor_small_modulus_base_tail_of_v4_successorSchedule_blocks
    (oddModulusToriV4SuccessorScheduleBlocksGoal_of_successorScheduleAddBlocks
      hBlocks)
    hb5 hmodd hm3 hmSmall hb

theorem odd_modulus_tori_all_dimensions_of_qeq1DegreeMatching
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Degree : PrefixCount.OrdinaryQeq1AuxDegreeMatrixGoal)
    (hQeq1Match : PrefixCount.OrdinaryQeq1SpecialMatchingGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_construction_blocks
    ⟨hQge2Closure,
      PrefixCount.ordinaryQeq1CanonicalCorrectionDataGoal_of_auxMatrix_and_specialMatching
        (PrefixCount.ordinaryQeq1AuxMatrixGoal_of_degreeMatrix hQeq1Degree)
        hQeq1Match,
      hReturn,
      hSmallPacket⟩
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qeq1UniformDegree
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Arith : PrefixCount.OrdinaryQeq1AuxDegreeArithmeticGoal)
    (hQeq1Uniform : PrefixCount.UniformColumnDegreeMatrixGoal)
    (hQeq1Match : PrefixCount.OrdinaryQeq1SpecialMatchingGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qeq1DegreeMatching
    hQge2Closure
    (PrefixCount.ordinaryQeq1AuxDegreeMatrixGoal_of_uniformColumnDegree
      hQeq1Arith hQeq1Uniform)
    hQeq1Match hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qeq1UniformTotal
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Total : PrefixCount.OrdinaryQeq1AuxDegreeTotalGoal)
    (hQeq1Uniform : PrefixCount.UniformColumnDegreeMatrixGoal)
    (hQeq1Match : PrefixCount.OrdinaryQeq1SpecialMatchingGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qeq1UniformDegree
    hQge2Closure
    (PrefixCount.ordinaryQeq1AuxDegreeArithmeticGoal_of_total hQeq1Total)
    hQeq1Uniform hQeq1Match hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qeq1PostTotal
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Uniform : PrefixCount.UniformColumnDegreeMatrixGoal)
    (hQeq1Match : PrefixCount.OrdinaryQeq1SpecialMatchingGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qeq1UniformTotal
    hQge2Closure PrefixCount.ordinaryQeq1AuxDegreeTotalGoal
    hQeq1Uniform hQeq1Match hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qeq1ResidueCount
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Residue : PrefixCount.UniformColumnDegreeResidueCountGoal)
    (hQeq1Match : PrefixCount.OrdinaryQeq1SpecialMatchingGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qeq1PostTotal
    hQge2Closure
    (PrefixCount.uniformColumnDegreeMatrixGoal_of_residueCount hQeq1Residue)
    hQeq1Match hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qeq1IntervalPartition
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Partition : PrefixCount.UniformColumnDegreeIntervalPartitionGoal)
    (hQeq1Match : PrefixCount.OrdinaryQeq1SpecialMatchingGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qeq1ResidueCount
    hQge2Closure
    (PrefixCount.uniformColumnDegreeResidueCountGoal_of_intervalPartition
      hQeq1Partition)
    hQeq1Match hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qeq1PostUniform
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Match : PrefixCount.OrdinaryQeq1SpecialMatchingGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qeq1IntervalPartition
    hQge2Closure PrefixCount.uniformColumnDegreeIntervalPartitionGoal
    hQeq1Match hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_degree_matching_blocks
    (hBlocks : OddModulusToriV4DegreeMatchingBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with
    ⟨hQge2Closure, hQeq1Degree, hQeq1Match, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qeq1DegreeMatching
      hQge2Closure hQeq1Degree hQeq1Match hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_uniform_degree_blocks
    (hBlocks : OddModulusToriV4UniformDegreeBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with
    ⟨hQge2Closure, hQeq1Arith, hQeq1Uniform,
      hQeq1Match, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qeq1UniformDegree
      hQge2Closure hQeq1Arith hQeq1Uniform
      hQeq1Match hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_uniform_total_blocks
    (hBlocks : OddModulusToriV4UniformTotalBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with
    ⟨hQge2Closure, hQeq1Total, hQeq1Uniform,
      hQeq1Match, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qeq1UniformTotal
      hQge2Closure hQeq1Total hQeq1Uniform
      hQeq1Match hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_post_total_blocks
    (hBlocks : OddModulusToriV4PostTotalBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with
    ⟨hQge2Closure, hQeq1Uniform, hQeq1Match, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qeq1PostTotal
      hQge2Closure hQeq1Uniform hQeq1Match
      hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_residue_blocks
    (hBlocks : OddModulusToriV4ResidueBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with
    ⟨hQge2Closure, hQeq1Residue, hQeq1Match, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qeq1ResidueCount
      hQge2Closure hQeq1Residue hQeq1Match
      hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_interval_blocks
    (hBlocks : OddModulusToriV4IntervalBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with
    ⟨hQge2Closure, hQeq1Partition, hQeq1Match, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qeq1IntervalPartition
      hQge2Closure hQeq1Partition hQeq1Match
      hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_post_uniform_blocks
    (hBlocks : OddModulusToriV4PostUniformBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with
    ⟨hQge2Closure, hQeq1Match, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qeq1PostUniform
      hQge2Closure hQeq1Match hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Matrix_geometry_and_slackPacketLift
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1SignedMatrixGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Matrix_and_geometry
      hQge2Matrix hQeq1Matrix hGeom)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Matrix_rootFlatCanonical_and_slackPacketLift
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1SignedMatrixGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Matrix_geometry_and_slackPacketLift
    hQge2Matrix hQeq1Matrix
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_transports_geometry_and_small_packet_lift
    (hQge2 : PrefixCount.TransportQge2Goal)
    (hQeq1 : PrefixCount.TransportQeq1Goal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (oddCoreHighModulusPrefixCountGoal_of_transports_and_geometry
      hQge2 hQeq1 hGeom)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_margins_geometry_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2Goal)
    (hQeq1 : PrefixCount.MarginTransportQeq1Goal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (oddCoreHighModulusPrefixCountGoal_of_margins_and_geometry
      hQge2 hQeq1 hGeom)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Margin_qeq1PlusFamily_geometry_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2Goal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (oddCoreHighModulusPrefixCountGoal_of_qge2Margin_qeq1PlusFamily_and_geometry
      hQge2 hQeq1 hGeom)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Margin_qeq1PlusFamily_rootFlatCanonical_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2Goal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (oddCoreHighModulusPrefixCountGoal_of_qge2Margin_qeq1PlusFamily_and_rootFlatCanonical
      hQge2 hQeq1 hReturn)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Compat_qeq1PlusFamily_geometry_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Margin_qeq1PlusFamily_geometry_and_small_packet_lift
    (PrefixCount.marginTransportQge2Goal_of_compatible hQge2)
    hQeq1 hGeom hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Compat_qeq1PlusFamily_rootFlatCanonical_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Margin_qeq1PlusFamily_rootFlatCanonical_and_small_packet_lift
    (PrefixCount.marginTransportQge2Goal_of_compatible hQge2)
    hQeq1 hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Compat_qeq1Compat_geometry_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1CompatibleGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (oddCoreHighModulusPrefixCountGoal_of_qge2Compat_qeq1Compat_and_geometry
      hQge2 hQeq1 hGeom)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Compat_qeq1Compat_rootFlatCanonical_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1CompatibleGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (oddCoreHighModulusPrefixCountGoal_of_qge2Compat_qeq1Compat_and_rootFlatCanonical
      hQge2 hQeq1 hReturn)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1Margin_geometry_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1Goal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_margins_geometry_and_small_packet_lift
    (PrefixCount.marginTransportQge2Goal_of_plan hQge2)
    hQeq1 hGeom hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1Compat_geometry_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1CompatibleGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1Margin_geometry_and_small_packet_lift
    hQge2
    (PrefixCount.marginTransportQeq1Goal_of_compatible hQeq1)
    hGeom hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1MatchedPMOne_geometry_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1MatchedPMOneGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1Compat_geometry_and_small_packet_lift
    hQge2
    (PrefixCount.marginTransportQeq1CompatibleGoal_of_matchedPMOne hQeq1)
    hGeom hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1PlusFamily_geometry_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1MatchedPMOne_geometry_and_small_packet_lift
    hQge2
    (PrefixCount.marginTransportQeq1MatchedPMOneGoal_of_plusFamily hQeq1)
    hGeom hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1PlusFamily_rootFlatCanonical_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1PlusFamily_and_rootFlatCanonical
      hQge2 hQeq1 hReturn)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2PlanParts_qeq1PlusFamily_geometry_and_small_packet_lift
    (hQge2Plan : PrefixCount.MarginPlanQge2Goal)
    (hQge2Matrix : PrefixCount.SignedMarginMatrixForQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1PlusFamily_geometry_and_small_packet_lift
    (PrefixCount.marginTransportQge2PlanGoal_of_plan_and_matrix
      hQge2Plan hQge2Matrix)
    hQeq1 hGeom hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2PlanParts_qeq1PlusFamily_rootFlat_and_small_packet_lift
    (hQge2Plan : PrefixCount.MarginPlanQge2Goal)
    (hQge2Matrix : PrefixCount.SignedMarginMatrixForQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatReturnGoal)
    (hLift : PrefixCountRootFlatCayleyLiftGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2PlanParts_qeq1PlusFamily_geometry_and_small_packet_lift
    hQge2Plan hQge2Matrix hQeq1
    (prefixCountGeometricCriterionGoal_of_rootFlat hReturn hLift)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2PlanParts_qeq1PlusFamily_rootFlatEquiv_and_small_packet_lift
    (hQge2Plan : PrefixCount.MarginPlanQge2Goal)
    (hQge2Matrix : PrefixCount.SignedMarginMatrixForQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatReturnGoal)
    (hEquiv : PrefixCountRootFlatEquivLiftGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2PlanParts_qeq1PlusFamily_rootFlat_and_small_packet_lift
    hQge2Plan hQge2Matrix hQeq1 hReturn
    (prefixCountRootFlatCayleyLiftGoal_of_equiv hEquiv)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2PlanParts_qeq1PlusFamily_rootFlatCanonical_and_small_packet_lift
    (hQge2Plan : PrefixCount.MarginPlanQge2Goal)
    (hQge2Matrix : PrefixCount.SignedMarginMatrixForQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (oddCoreHighModulusPrefixCountGoal_of_qge2PlanParts_qeq1PlusFamily_and_rootFlatCanonical
      hQge2Plan hQge2Matrix hQeq1 hReturn)
    hSmallPacket hd2 hmodd hm3

end Concrete
end RoundComposite
