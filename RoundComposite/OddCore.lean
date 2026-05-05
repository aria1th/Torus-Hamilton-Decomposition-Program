import RoundComposite.BaseTailGeometry
import RoundComposite.FiniteHoffman.EdgeColoring
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

def prefixCountRootAgreeUpTo {d m : Nat} (k : Nat)
    (w v : PrefixCountRootState d m) : Prop :=
  ∀ j : Fin (d - 1), j.val ≤ k → w j = v j

theorem prefixCountRootAgreeUpTo_refl {d m : Nat} (k : Nat)
    (w : PrefixCountRootState d m) :
    prefixCountRootAgreeUpTo k w w := by
  intro _j _hj
  rfl

theorem prefixCountRootAgreeUpTo_symm {d m : Nat} {k : Nat}
    {w v : PrefixCountRootState d m}
    (h : prefixCountRootAgreeUpTo k w v) :
    prefixCountRootAgreeUpTo k v w := by
  intro j hj
  exact (h j hj).symm

theorem prefixCountRootAgreeUpTo_trans {d m : Nat} {k : Nat}
    {u v w : PrefixCountRootState d m}
    (huv : prefixCountRootAgreeUpTo k u v)
    (hvw : prefixCountRootAgreeUpTo k v w) :
    prefixCountRootAgreeUpTo k u w := by
  intro j hj
  exact (huv j hj).trans (hvw j hj)

theorem prefixCountRootAgreeUpTo_mono {d m : Nat} {k l : Nat}
    {w v : PrefixCountRootState d m}
    (hkl : k ≤ l) (h : prefixCountRootAgreeUpTo l w v) :
    prefixCountRootAgreeUpTo k w v := by
  intro j hj
  exact h j (hj.trans hkl)

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

theorem prefixCountRootStateHeadTailEquiv_symm_eq_of_take_le
    {d m : Nat} (hd2 : 2 ≤ d) {z : ZMod m}
    {x y : Fin (d - 2) → ZMod m} {k : Nat} (hk : k < d - 2)
    (hxy :
      Shared.zmodVectorTake (Nat.le_of_lt hk) x =
        Shared.zmodVectorTake (Nat.le_of_lt hk) y)
    {j : Fin (d - 1)} (hj : j.val ≤ k) :
    (prefixCountRootStateHeadTailEquiv d m hd2).symm (z, x) j =
      (prefixCountRootStateHeadTailEquiv d m hd2).symm (z, y) j := by
  by_cases hj0 : j.val = 0
  · have hidx : j = ⟨0, by omega⟩ := Fin.ext hj0
    rw [hidx]
    simp
  · have hjpred : j.val - 1 < k := by omega
    have htail := congrFun hxy ⟨j.val - 1, hjpred⟩
    have hidx :
        (⟨(j.val - 1) + 1, by omega⟩ : Fin (d - 1)) = j := by
      apply Fin.ext
      simp
      omega
    have hxidx :
        (⟨j.val - 1, lt_of_lt_of_le hjpred (Nat.le_of_lt hk)⟩ :
            Fin (d - 2)) =
          ⟨(⟨(j.val - 1) + 1, by omega⟩ : Fin (d - 1)).val - 1,
            by omega⟩ := by
      apply Fin.ext
      simp
    rw [← hidx]
    simpa [prefixCountRootStateHeadTailEquiv, hj0, hxidx,
      Shared.zmodVectorTake] using htail

theorem prefixCountRootAgreeUpTo_headTail_symm_of_take
    {d m : Nat} (hd2 : 2 ≤ d) {z : ZMod m}
    {x y : Fin (d - 2) → ZMod m} {k : Nat} (hk : k < d - 2)
    (hxy :
      Shared.zmodVectorTake (Nat.le_of_lt hk) x =
        Shared.zmodVectorTake (Nat.le_of_lt hk) y) :
    prefixCountRootAgreeUpTo k
      ((prefixCountRootStateHeadTailEquiv d m hd2).symm (z, x))
      ((prefixCountRootStateHeadTailEquiv d m hd2).symm (z, y)) := by
  intro j hj
  exact prefixCountRootStateHeadTailEquiv_symm_eq_of_take_le
    hd2 hk hxy hj

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
  by_cases hs0 : s.val = 0
  · have hLambda : (prefixCountLambdaRho d rho s).val = 0 := by
      rw [prefixCountLambdaRho_eq_self_of_val_zero rho hs0]
      exact hs0
    constructor
    · intro h
      omega
    · intro hcase
      rcases hcase with ⟨hs, _⟩ | ⟨hs, hspos, _⟩ | ⟨hs, _⟩ <;> omega
  · by_cases hs1 : s.val = 1
    · have hLambda : (prefixCountLambdaRho d rho s).val = rho.val := by
        rw [prefixCountLambdaRho_eq_rho_of_val_one rho hs1]
      constructor
      · intro h
        exact Or.inl ⟨hs1, by omega⟩
      · intro hcase
        rcases hcase with ⟨_hs, hrho⟩ | ⟨hs, hspos, _⟩ | ⟨hs, _⟩
        · omega
        · omega
        · omega
    · by_cases hlt : rho.val < s.val
      · have hLambda : (prefixCountLambdaRho d rho s).val = s.val := by
          rw [prefixCountLambdaRho_eq_self_of_rho_lt rho hs0 hs1 hlt]
        constructor
        · intro h
          rw [hLambda] at h
          exact Or.inr (Or.inl ⟨by omega, by omega, hlt⟩)
        · intro hcase
          rw [hLambda]
          rcases hcase with ⟨hs, _⟩ | ⟨hs, _hspos, _hrho⟩ | ⟨hs, _⟩
          · omega
          · exact hs
          · omega
      · have hLambda : (prefixCountLambdaRho d rho s).val = s.val - 1 :=
          prefixCountLambdaRho_val_eq_pred rho hs0 hs1 hlt
        constructor
        · intro h
          rw [hLambda] at h
          exact Or.inr (Or.inr ⟨by omega, hlt⟩)
        · intro hcase
          rw [hLambda]
          rcases hcase with ⟨hs, _⟩ | ⟨_hs, _hspos, hrho⟩ | ⟨hs, _hrho⟩
          · omega
          · exact False.elim (hlt hrho)
          · omega

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

theorem prefixCountLayerCount_range_eq_matrix
    {d m : Nat} [NeZero m] {M : Matrix (Fin d) (Fin d) Nat}
    (L : PrefixCount.LayerPermCounts d m M) (c s : Fin d) :
    (∑ t ∈ Finset.range m,
        if L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c = s
        then (1 : Nat) else 0) = M c s := by
  let fNat : Nat → Nat := fun t =>
    if L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c = s
    then 1 else 0
  calc
    (∑ t ∈ Finset.range m,
        if L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c = s
        then (1 : Nat) else 0)
        = ∑ t ∈ Finset.range m, fNat t := rfl
    _ = ∑ t : Fin m, fNat t.val := by
          rw [Fin.sum_univ_eq_sum_range fNat m]
    _ = ∑ t : Fin m, if L.layer t c = s then (1 : Nat) else 0 := by
          apply Finset.sum_congr rfl
          intro t _ht
          simp [fNat, prefixCountLayerIndex_natCast_val]
    _ = M c s := L.count_eq c s

theorem prefixCountLayerCount_range_eq_matrix_zmod
    {d m : Nat} [NeZero m] {M : Matrix (Fin d) (Fin d) Nat}
    (L : PrefixCount.LayerPermCounts d m M) (c s : Fin d) :
    (∑ t ∈ Finset.range m,
        if L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c = s
        then (1 : ZMod m) else 0) = (M c s : ZMod m) := by
  let fNat : Nat → Nat := fun t =>
    if L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c = s
    then 1 else 0
  have hNat :
      (∑ t ∈ Finset.range m, fNat t) = M c s := by
    simpa [fNat] using
      prefixCountLayerCount_range_eq_matrix (m := m) L c s
  have hCast :
      ((∑ t ∈ Finset.range m, fNat t : Nat) : ZMod m) =
        ∑ t ∈ Finset.range m,
          if L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c = s
          then (1 : ZMod m) else 0 := by
    simp [fNat]
  rw [← hCast, hNat]

theorem prefixCount_toMatrix_colStep_sub_colDelta_zmod
    {d m : Nat} (hd2 : 2 ≤ d) (C : PrefixCount.Parts d)
    (c : Fin d) (k : Fin (d - 2)) :
    (((C.toMatrix hd2) c (PrefixCount.Parts.colStep hd2 k) : Nat) : ZMod m) -
        (((C.toMatrix hd2) c (PrefixCount.Parts.colDelta hd2) : Nat) :
          ZMod m) =
      (((C.step c k : Int) - (C.delta c : Int)) : ZMod m) := by
  simp [Int.cast_natCast]

theorem prefixCount_toMatrix_rawStep_sub_delta_zmod
    {d m : Nat} (hd2 : 2 ≤ d) (C : PrefixCount.Parts d)
    (c : Fin d) {k : Nat} (hk : k < d - 2) :
    (((C.toMatrix hd2) c ⟨k + 2, by omega⟩ : Nat) : ZMod m) -
        (((C.toMatrix hd2) c ⟨1, by omega⟩ : Nat) : ZMod m) =
      (((C.step c ⟨k, hk⟩ : Int) - (C.delta c : Int)) : ZMod m) := by
  simpa [PrefixCount.Parts.colStep, PrefixCount.Parts.colDelta] using
    prefixCount_toMatrix_colStep_sub_colDelta_zmod
      (m := m) hd2 C c ⟨k, hk⟩

abbrev prefixCountReturnTailDeltaCol {d : Nat} (hd2 : 2 ≤ d) : Fin d :=
  PrefixCount.Parts.colDelta hd2

abbrev prefixCountReturnTailStepCol
    {d : Nat} (hd2 : 2 ≤ d) {k : Nat} (hk : k < d - 2) : Fin d :=
  PrefixCount.Parts.colStep hd2 ⟨k, hk⟩

def prefixCountReturnTailSignedCoeff
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {k : Nat} (hk : k < d - 2) (s : Fin d) : ZMod m :=
  ((-1 : ZMod m) ^ (k + 1)) *
    ((if s = prefixCountReturnTailStepCol hd2 hk then (1 : ZMod m) else 0) -
      if s = prefixCountReturnTailDeltaCol hd2 then (1 : ZMod m) else 0)

theorem prefixCountReturnTailSignedCoeff_layer_sum_eq_matrix
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) {k : Nat} (hk : k < d - 2) :
    (∑ t ∈ Finset.range m,
      prefixCountReturnTailSignedCoeff hd2 hk
        (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c)) =
      ((-1 : ZMod m) ^ (k + 1)) *
        ((((C.toMatrix hd2)
            c (prefixCountReturnTailStepCol hd2 hk) : Nat) : ZMod m) -
          (((C.toMatrix hd2)
            c (prefixCountReturnTailDeltaCol hd2) : Nat) : ZMod m)) := by
  classical
  let eps : ZMod m := (-1 : ZMod m) ^ (k + 1)
  let stepCol : Fin d := prefixCountReturnTailStepCol hd2 hk
  let deltaCol : Fin d := prefixCountReturnTailDeltaCol hd2
  calc
    (∑ t ∈ Finset.range m,
      prefixCountReturnTailSignedCoeff hd2 hk
        (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c))
        =
        (∑ t ∈ Finset.range m,
          eps *
            ((if L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c =
                stepCol then (1 : ZMod m) else 0) -
              if L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c =
                deltaCol then (1 : ZMod m) else 0)) := by
          simp [prefixCountReturnTailSignedCoeff, eps, stepCol, deltaCol,
            eq_comm]
    _ =
        eps *
          (∑ t ∈ Finset.range m,
            ((if L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c =
                stepCol then (1 : ZMod m) else 0) -
              if L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c =
                deltaCol then (1 : ZMod m) else 0)) := by
          rw [Finset.mul_sum]
    _ =
        eps *
          ((∑ t ∈ Finset.range m,
              if L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c =
                stepCol then (1 : ZMod m) else 0) -
            (∑ t ∈ Finset.range m,
              if L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c =
                deltaCol then (1 : ZMod m) else 0)) := by
          rw [Finset.sum_sub_distrib]
    _ =
        eps *
          ((((C.toMatrix hd2) c stepCol : Nat) : ZMod m) -
            (((C.toMatrix hd2) c deltaCol : Nat) : ZMod m)) := by
          rw [prefixCountLayerCount_range_eq_matrix_zmod
            (m := m) L c stepCol]
          rw [prefixCountLayerCount_range_eq_matrix_zmod
            (m := m) L c deltaCol]
    _ =
      ((-1 : ZMod m) ^ (k + 1)) *
        ((((C.toMatrix hd2)
            c (prefixCountReturnTailStepCol hd2 hk) : Nat) : ZMod m) -
          (((C.toMatrix hd2)
            c (prefixCountReturnTailDeltaCol hd2) : Nat) : ZMod m)) := by
          rfl

theorem prefixCountNoHitSubtypeCard
    {m n : Nat} [NeZero m] (t : ZMod m) :
    Fintype.card {x : Fin n → ZMod m // ∀ i : Fin n, x i ≠ t} =
      (m - 1) ^ n := by
  classical
  let e :
      {x : Fin n → ZMod m // ∀ i : Fin n, x i ≠ t} ≃
        (Fin n → {a : ZMod m // a ≠ t}) :=
  { toFun := fun x i => ⟨x.1 i, x.2 i⟩
    invFun := fun y => ⟨fun i => (y i).1, fun i => (y i).2⟩
    left_inv := by
      intro x
      ext i
      rfl
    right_inv := by
      intro y
      ext i
      rfl }
  calc
    Fintype.card {x : Fin n → ZMod m // ∀ i : Fin n, x i ≠ t}
        = Fintype.card (Fin n → {a : ZMod m // a ≠ t}) :=
          Fintype.card_congr e
    _ = Fintype.card {a : ZMod m // a ≠ t} ^ n := by
          simp
    _ = (m - 1) ^ n := by
          have hsub :
              Fintype.card {a : ZMod m // a ≠ t} = m - 1 := by
            have hcompl :=
              Fintype.card_subtype_compl (fun a : ZMod m => a = t)
            rw [Fintype.card_subtype_eq t] at hcompl
            rw [ZMod.card m] at hcompl
            exact hcompl
          rw [hsub]

theorem prefixCountNoHitIndicatorSum
    {m n : Nat} [NeZero m] (t : ZMod m) :
    (∑ x : (Fin n → ZMod m),
        if (∀ i : Fin n, x i ≠ t) then (1 : ZMod m) else 0) =
      (-1 : ZMod m) ^ n := by
  classical
  calc
    (∑ x : (Fin n → ZMod m),
        if (∀ i : Fin n, x i ≠ t) then (1 : ZMod m) else 0)
        =
        ((Fintype.card {x : Fin n → ZMod m // ∀ i : Fin n, x i ≠ t}) :
          ZMod m) := by
          simp [Fintype.card_subtype]
    _ = (((m - 1) ^ n : Nat) : ZMod m) := by
          rw [prefixCountNoHitSubtypeCard (m := m) (n := n) t]
    _ = (-1 : ZMod m) ^ n := by
          rw [Nat.cast_pow]
          have hbase : ((m - 1 : Nat) : ZMod m) = (-1 : ZMod m) := by
            rw [Nat.cast_pred (NeZero.pos m)]
            simp
          rw [hbase]

theorem prefixCountHasHitIndicatorSum
    {m n : Nat} [NeZero m] (hn : 0 < n) (t : ZMod m) :
    (∑ x : (Fin n → ZMod m),
        if (∃ i : Fin n, x i = t) then (1 : ZMod m) else 0) =
      -((-1 : ZMod m) ^ n) := by
  classical
  have hall : (∑ x : (Fin n → ZMod m), (1 : ZMod m)) = 0 := by
    calc
      (∑ x : (Fin n → ZMod m), (1 : ZMod m))
          = (Fintype.card (Fin n → ZMod m) : ZMod m) := by
            simp
      _ = ((m ^ n : Nat) : ZMod m) := by
            simp [ZMod.card]
      _ = 0 := by
            rw [Nat.cast_pow]
            simp [hn.ne']
  have hno := prefixCountNoHitIndicatorSum (m := m) (n := n) t
  have hsplit :
      (∑ x : (Fin n → ZMod m),
          if (∃ i : Fin n, x i = t) then (1 : ZMod m) else 0) +
        (∑ x : (Fin n → ZMod m),
          if (∀ i : Fin n, x i ≠ t) then (1 : ZMod m) else 0) =
        (∑ x : (Fin n → ZMod m), (1 : ZMod m)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    by_cases hhit : ∃ i : Fin n, x i = t
    · have hnall : ¬ ∀ i : Fin n, x i ≠ t := by
        intro hno
        rcases hhit with ⟨i, hi⟩
        exact hno i hi
      simp [hhit, hnall]
    · have hallno : ∀ i : Fin n, x i ≠ t := by
        intro i hi
        exact hhit ⟨i, hi⟩
      simp [hallno]
  have hzero :
      (∑ x : (Fin n → ZMod m),
          if (∃ i : Fin n, x i = t) then (1 : ZMod m) else 0) +
        (-1 : ZMod m) ^ n = 0 := by
    simpa [hno, hall] using hsplit
  exact eq_neg_of_add_eq_zero_left hzero

theorem prefixCountPairFreeLastIndicatorSum_zero
    {m n : Nat} [NeZero m]
    (P : (Fin n → ZMod m) → Prop) [DecidablePred P] :
    (∑ p : (Fin n → ZMod m) × ZMod m,
        if P p.1 then (1 : ZMod m) else 0) = 0 := by
  classical
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro x _hx
  by_cases hx : P x
  · simp [hx]
  · simp [hx]

theorem prefixCountPairFirstHitLastIndicatorSum
    {m n : Nat} [NeZero m] (t : ZMod m) :
    (∑ p : (Fin n → ZMod m) × ZMod m,
        if (∀ i : Fin n, p.1 i ≠ t) ∧ p.2 = t
        then (1 : ZMod m) else 0) =
      (-1 : ZMod m) ^ n := by
  classical
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : Fin n → ZMod m, ∑ a : ZMod m,
        if (∀ i : Fin n, x i ≠ t) ∧ a = t
        then (1 : ZMod m) else 0)
        =
        ∑ x : Fin n → ZMod m,
          if (∀ i : Fin n, x i ≠ t) then (1 : ZMod m) else 0 := by
          apply Finset.sum_congr rfl
          intro x _hx
          by_cases hx : ∀ i : Fin n, x i ≠ t
          · simp [hx]
          · simp [hx]
    _ = (-1 : ZMod m) ^ n :=
          prefixCountNoHitIndicatorSum (m := m) (n := n) t

abbrev prefixCountPcNoZero {m n : Nat}
    (y : Fin n → ZMod m) : Prop :=
  ∀ i : Fin n, y i ≠ 0

abbrev prefixCountPcSomeZero {m n : Nat}
    (y : Fin n → ZMod m) : Prop :=
  ∃ i : Fin n, y i = 0

abbrev prefixCountPcExactLastZero {m k : Nat}
    (y : Fin (k + 1) → ZMod m) : Prop :=
  (∀ i : Fin k, y i.castSucc ≠ 0) ∧ y (Fin.last k) = 0

abbrev prefixCountPcHitBeforeLastZero {m k : Nat}
    (y : Fin (k + 1) → ZMod m) : Prop :=
  ∃ i : Fin k, y i.castSucc = 0

theorem prefixCountPcNoZeroIndicatorSum
    {m n : Nat} [NeZero m] :
    (∑ y : Fin n → ZMod m,
        if prefixCountPcNoZero y then (1 : ZMod m) else 0) =
      (-1 : ZMod m) ^ n := by
  simpa [prefixCountPcNoZero] using
    prefixCountNoHitIndicatorSum (m := m) (n := n) (0 : ZMod m)

theorem prefixCountPcSomeZeroIndicatorSum
    {m n : Nat} [NeZero m] (hn : 0 < n) :
    (∑ y : Fin n → ZMod m,
        if prefixCountPcSomeZero y then (1 : ZMod m) else 0) =
      -((-1 : ZMod m) ^ n) := by
  simpa [prefixCountPcSomeZero] using
    prefixCountHasHitIndicatorSum (m := m) (n := n) hn (0 : ZMod m)

theorem prefixCountPcExactLastZeroIndicatorSum
    {m k : Nat} [NeZero m] :
    (∑ y : Fin (k + 1) → ZMod m,
        if prefixCountPcExactLastZero y then (1 : ZMod m) else 0) =
      -((-1 : ZMod m) ^ (k + 1)) := by
  classical
  let e := Shared.zmodVectorSnocEquiv k m
  calc
    (∑ y : Fin (k + 1) → ZMod m,
        if prefixCountPcExactLastZero y then (1 : ZMod m) else 0)
        =
        ∑ p : (Fin k → ZMod m) × ZMod m,
          if (∀ i : Fin k, p.1 i ≠ 0) ∧ p.2 = 0
          then (1 : ZMod m) else 0 := by
          exact Fintype.sum_equiv e
            (fun y =>
              if prefixCountPcExactLastZero y then (1 : ZMod m) else 0)
            (fun p =>
              if (∀ i : Fin k, p.1 i ≠ 0) ∧ p.2 = 0
              then (1 : ZMod m) else 0)
            (by
              intro y
              have hp :
                  ((∀ i : Fin k, y i.castSucc ≠ 0) ∧
                      y (Fin.last k) = 0) ↔
                    ((∀ i : Fin k, Fin.init y i ≠ 0) ∧
                      y (Fin.last k) = 0) := by
                constructor
                · intro h
                  exact ⟨fun i => by simpa [Fin.init] using h.1 i, h.2⟩
                · intro h
                  exact ⟨fun i => by simpa [Fin.init] using h.1 i, h.2⟩
              by_cases hP :
                  (∀ i : Fin k, y i.castSucc ≠ 0) ∧
                    y (Fin.last k) = 0
              · have hQ :
                    (∀ i : Fin k, Fin.init y i ≠ 0) ∧
                      y (Fin.last k) = 0 := hp.mp hP
                simp [e, prefixCountPcExactLastZero,
                  Shared.zmodVectorSnocEquiv, hP, hQ]
              · have hQ :
                    ¬ ((∀ i : Fin k, Fin.init y i ≠ 0) ∧
                      y (Fin.last k) = 0) := by
                  intro hQ
                  exact hP (hp.mpr hQ)
                simp [e, prefixCountPcExactLastZero,
                  Shared.zmodVectorSnocEquiv, hP, hQ])
    _ = (-1 : ZMod m) ^ k :=
          prefixCountPairFirstHitLastIndicatorSum
            (m := m) (n := k) (0 : ZMod m)
    _ = -((-1 : ZMod m) ^ (k + 1)) := by
          rw [pow_succ]
          ring

theorem prefixCountPcHitBeforeLastZeroIndicatorSum
    {m k : Nat} [NeZero m] :
    (∑ y : Fin (k + 1) → ZMod m,
        if prefixCountPcHitBeforeLastZero y then (1 : ZMod m) else 0) =
      0 := by
  classical
  let e := Shared.zmodVectorSnocEquiv k m
  calc
    (∑ y : Fin (k + 1) → ZMod m,
        if prefixCountPcHitBeforeLastZero y then (1 : ZMod m) else 0)
        =
        ∑ p : (Fin k → ZMod m) × ZMod m,
          if (∃ i : Fin k, p.1 i = 0)
          then (1 : ZMod m) else 0 := by
          exact Fintype.sum_equiv e
            (fun y =>
              if prefixCountPcHitBeforeLastZero y then (1 : ZMod m) else 0)
            (fun p =>
              if (∃ i : Fin k, p.1 i = 0)
              then (1 : ZMod m) else 0)
            (by
              intro y
              have hp :
                  (∃ i : Fin k, y i.castSucc = 0) ↔
                    ∃ i : Fin k, Fin.init y i = 0 := by
                constructor
                · intro h
                  rcases h with ⟨i, hi⟩
                  exact ⟨i, by simpa [Fin.init] using hi⟩
                · intro h
                  rcases h with ⟨i, hi⟩
                  exact ⟨i, by simpa [Fin.init] using hi⟩
              by_cases hP : ∃ i : Fin k, y i.castSucc = 0
              · have hQ : ∃ i : Fin k, Fin.init y i = 0 := hp.mp hP
                simp [e, prefixCountPcHitBeforeLastZero,
                  Shared.zmodVectorSnocEquiv, hP, hQ]
              · have hQ : ¬ ∃ i : Fin k, Fin.init y i = 0 := by
                  intro hQ
                  exact hP (hp.mpr hQ)
                simp [e, prefixCountPcHitBeforeLastZero,
                  Shared.zmodVectorSnocEquiv, hP, hQ])
    _ = 0 :=
          prefixCountPairFreeLastIndicatorSum_zero
            (m := m) (n := k)
            (P := fun x : Fin k → ZMod m => ∃ i : Fin k, x i = 0)

theorem prefixCountReturnTailLocalSymbolSplitIndicatorSum
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {k : Nat} (hk : k < d - 2) (s : Fin d) :
    (∑ y : Fin (k + 1) → ZMod m,
        if
          (s = prefixCountReturnTailDeltaCol hd2 ∧
              prefixCountPcExactLastZero y) ∨
            (s.val = k + 1 ∧ 1 < s.val ∧
              prefixCountPcHitBeforeLastZero y) ∨
            (s = prefixCountReturnTailStepCol hd2 hk ∧
              prefixCountPcNoZero y)
        then (1 : ZMod m) else 0) =
      prefixCountReturnTailSignedCoeff hd2 hk s := by
  classical
  have hDeltaStep :
      prefixCountReturnTailDeltaCol hd2 ≠
        prefixCountReturnTailStepCol hd2 hk := by
    intro h
    have hval := congrArg Fin.val h
    simp [prefixCountReturnTailDeltaCol, prefixCountReturnTailStepCol,
      PrefixCount.Parts.colDelta, PrefixCount.Parts.colStep] at hval
  by_cases hDelta : s = prefixCountReturnTailDeltaCol hd2
  · have hNotStep : s ≠ prefixCountReturnTailStepCol hd2 hk := by
      intro hStep
      exact hDeltaStep (hDelta.symm.trans hStep)
    have hNotMiddle : ¬ (s.val = k + 1 ∧ 1 < s.val) := by
      intro h
      have hsval : s.val = 1 := by
        simpa [hDelta, prefixCountReturnTailDeltaCol,
          PrefixCount.Parts.colDelta]
      omega
    calc
      (∑ y : Fin (k + 1) → ZMod m,
          if
            (s = prefixCountReturnTailDeltaCol hd2 ∧
                prefixCountPcExactLastZero y) ∨
              (s.val = k + 1 ∧ 1 < s.val ∧
                prefixCountPcHitBeforeLastZero y) ∨
              (s = prefixCountReturnTailStepCol hd2 hk ∧
                prefixCountPcNoZero y)
          then (1 : ZMod m) else 0)
          =
          ∑ y : Fin (k + 1) → ZMod m,
            if prefixCountPcExactLastZero y then (1 : ZMod m) else 0 := by
            apply Finset.sum_congr rfl
            intro y _hy
            have hiff :
                ((s = prefixCountReturnTailDeltaCol hd2 ∧
                    prefixCountPcExactLastZero y) ∨
                  (s.val = k + 1 ∧ 1 < s.val ∧
                    prefixCountPcHitBeforeLastZero y) ∨
                  (s = prefixCountReturnTailStepCol hd2 hk ∧
                    prefixCountPcNoZero y)) ↔
                  prefixCountPcExactLastZero y := by
              constructor
              · intro h
                rcases h with h | h | h
                · exact h.2
                · exact False.elim (hNotMiddle ⟨h.1, h.2.1⟩)
                · exact False.elim (hNotStep h.1)
              · intro hy
                exact Or.inl ⟨hDelta, hy⟩
            by_cases hP :
                (s = prefixCountReturnTailDeltaCol hd2 ∧
                    prefixCountPcExactLastZero y) ∨
                  (s.val = k + 1 ∧ 1 < s.val ∧
                    prefixCountPcHitBeforeLastZero y) ∨
                  (s = prefixCountReturnTailStepCol hd2 hk ∧
                    prefixCountPcNoZero y)
            · have hy : prefixCountPcExactLastZero y := hiff.mp hP
              rw [if_pos hP, if_pos hy]
            · have hy : ¬ prefixCountPcExactLastZero y := by
                intro hy
                exact hP (hiff.mpr hy)
              rw [if_neg hP, if_neg hy]
      _ = prefixCountReturnTailSignedCoeff hd2 hk s := by
            rw [prefixCountPcExactLastZeroIndicatorSum]
            simp [prefixCountReturnTailSignedCoeff, hDelta, hDeltaStep]
  · by_cases hStep : s = prefixCountReturnTailStepCol hd2 hk
    · have hNotMiddle : ¬ (s.val = k + 1 ∧ 1 < s.val) := by
        intro h
        have hsval : s.val = k + 2 := by
          simpa [hStep, prefixCountReturnTailStepCol,
            PrefixCount.Parts.colStep]
        omega
      calc
        (∑ y : Fin (k + 1) → ZMod m,
            if
              (s = prefixCountReturnTailDeltaCol hd2 ∧
                  prefixCountPcExactLastZero y) ∨
                (s.val = k + 1 ∧ 1 < s.val ∧
                  prefixCountPcHitBeforeLastZero y) ∨
                (s = prefixCountReturnTailStepCol hd2 hk ∧
                  prefixCountPcNoZero y)
            then (1 : ZMod m) else 0)
            =
            ∑ y : Fin (k + 1) → ZMod m,
              if prefixCountPcNoZero y then (1 : ZMod m) else 0 := by
              apply Finset.sum_congr rfl
              intro y _hy
              have hiff :
                  ((s = prefixCountReturnTailDeltaCol hd2 ∧
                      prefixCountPcExactLastZero y) ∨
                    (s.val = k + 1 ∧ 1 < s.val ∧
                      prefixCountPcHitBeforeLastZero y) ∨
                    (s = prefixCountReturnTailStepCol hd2 hk ∧
                      prefixCountPcNoZero y)) ↔
                    prefixCountPcNoZero y := by
                constructor
                · intro h
                  rcases h with h | h | h
                  · exact False.elim (hDelta h.1)
                  · exact False.elim (hNotMiddle ⟨h.1, h.2.1⟩)
                  · exact h.2
                · intro hy
                  exact Or.inr (Or.inr ⟨hStep, hy⟩)
              by_cases hP :
                  (s = prefixCountReturnTailDeltaCol hd2 ∧
                      prefixCountPcExactLastZero y) ∨
                    (s.val = k + 1 ∧ 1 < s.val ∧
                      prefixCountPcHitBeforeLastZero y) ∨
                    (s = prefixCountReturnTailStepCol hd2 hk ∧
                      prefixCountPcNoZero y)
              · have hy : prefixCountPcNoZero y := hiff.mp hP
                rw [if_pos hP, if_pos hy]
              · have hy : ¬ prefixCountPcNoZero y := by
                  intro hy
                  exact hP (hiff.mpr hy)
                rw [if_neg hP, if_neg hy]
        _ = prefixCountReturnTailSignedCoeff hd2 hk s := by
              rw [prefixCountPcNoZeroIndicatorSum]
              have hStepDelta :
                  prefixCountReturnTailStepCol hd2 hk ≠
                    prefixCountReturnTailDeltaCol hd2 :=
                hDeltaStep ∘ Eq.symm
              simp [prefixCountReturnTailSignedCoeff, hStep, hStepDelta]
    · by_cases hMiddle : s.val = k + 1 ∧ 1 < s.val
      · calc
          (∑ y : Fin (k + 1) → ZMod m,
              if
                (s = prefixCountReturnTailDeltaCol hd2 ∧
                    prefixCountPcExactLastZero y) ∨
                  (s.val = k + 1 ∧ 1 < s.val ∧
                    prefixCountPcHitBeforeLastZero y) ∨
                  (s = prefixCountReturnTailStepCol hd2 hk ∧
                    prefixCountPcNoZero y)
              then (1 : ZMod m) else 0)
              =
              ∑ y : Fin (k + 1) → ZMod m,
                if prefixCountPcHitBeforeLastZero y
                then (1 : ZMod m) else 0 := by
                apply Finset.sum_congr rfl
                intro y _hy
                have hiff :
                    ((s = prefixCountReturnTailDeltaCol hd2 ∧
                        prefixCountPcExactLastZero y) ∨
                      (s.val = k + 1 ∧ 1 < s.val ∧
                        prefixCountPcHitBeforeLastZero y) ∨
                      (s = prefixCountReturnTailStepCol hd2 hk ∧
                        prefixCountPcNoZero y)) ↔
                      prefixCountPcHitBeforeLastZero y := by
                  constructor
                  · intro h
                    rcases h with h | h | h
                    · exact False.elim (hDelta h.1)
                    · exact h.2.2
                    · exact False.elim (hStep h.1)
                  · intro hy
                    exact Or.inr (Or.inl ⟨hMiddle.1, hMiddle.2, hy⟩)
                by_cases hP :
                    (s = prefixCountReturnTailDeltaCol hd2 ∧
                        prefixCountPcExactLastZero y) ∨
                      (s.val = k + 1 ∧ 1 < s.val ∧
                        prefixCountPcHitBeforeLastZero y) ∨
                      (s = prefixCountReturnTailStepCol hd2 hk ∧
                        prefixCountPcNoZero y)
                · have hy : prefixCountPcHitBeforeLastZero y := hiff.mp hP
                  rw [if_pos hP, if_pos hy]
                · have hy : ¬ prefixCountPcHitBeforeLastZero y := by
                    intro hy
                    exact hP (hiff.mpr hy)
                  rw [if_neg hP, if_neg hy]
          _ = prefixCountReturnTailSignedCoeff hd2 hk s := by
                rw [prefixCountPcHitBeforeLastZeroIndicatorSum]
                simp [prefixCountReturnTailSignedCoeff, hDelta, hStep]
      · calc
          (∑ y : Fin (k + 1) → ZMod m,
              if
                (s = prefixCountReturnTailDeltaCol hd2 ∧
                    prefixCountPcExactLastZero y) ∨
                  (s.val = k + 1 ∧ 1 < s.val ∧
                    prefixCountPcHitBeforeLastZero y) ∨
                  (s = prefixCountReturnTailStepCol hd2 hk ∧
                    prefixCountPcNoZero y)
              then (1 : ZMod m) else 0)
              =
              ∑ y : Fin (k + 1) → ZMod m, 0 := by
                apply Finset.sum_congr rfl
                intro y _hy
                have hNoMiddle :
                    ¬ (s.val = k + 1 ∧ 1 < s.val ∧
                        prefixCountPcHitBeforeLastZero y) := by
                  intro h
                  exact hMiddle ⟨h.1, h.2.1⟩
                simp [hDelta, hStep, hNoMiddle]
          _ = prefixCountReturnTailSignedCoeff hd2 hk s := by
                simp [prefixCountReturnTailSignedCoeff, hDelta, hStep]

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

theorem prefixCountCanonicalRhoHit_congr
    {d m : Nat} {t : ZMod m} {w v : PrefixCountRootState d m}
    {j : Fin (d - 1)} (h : w j = v j) :
    prefixCountCanonicalRhoHit t w j ↔
      prefixCountCanonicalRhoHit t v j := by
  constructor
  · intro hj
    exact ⟨hj.1, by simpa [h] using hj.2⟩
  · intro hj
    exact ⟨hj.1, by simpa [h] using hj.2⟩

theorem prefixCountCanonicalRhoHitNat_congr
    {d m : Nat} {t : ZMod m} {w v : PrefixCountRootState d m}
    {j : Nat}
    (h : ∀ hj : j < d - 1, w ⟨j, hj⟩ = v ⟨j, hj⟩) :
    prefixCountCanonicalRhoHitNat t w j ↔
      prefixCountCanonicalRhoHitNat t v j := by
  constructor
  · intro hj
    rcases hj with ⟨hjlt, hnext, hw⟩
    exact ⟨hjlt, hnext, by simpa [h hjlt] using hw⟩
  · intro hj
    rcases hj with ⟨hjlt, hnext, hv⟩
    exact ⟨hjlt, hnext, by simpa [h hjlt] using hv⟩

theorem prefixCountCanonicalRhoHit_congr_of_agreeUpTo
    {d m : Nat} {t : ZMod m} {w v : PrefixCountRootState d m}
    {k : Nat} (h : prefixCountRootAgreeUpTo k w v)
    {j : Fin (d - 1)} (hj : j.val ≤ k) :
    prefixCountCanonicalRhoHit t w j ↔
      prefixCountCanonicalRhoHit t v j :=
  prefixCountCanonicalRhoHit_congr (h j hj)

theorem prefixCountCanonicalRhoHitNat_congr_of_agreeUpTo
    {d m : Nat} {t : ZMod m} {w v : PrefixCountRootState d m}
    {k j : Nat} (h : prefixCountRootAgreeUpTo k w v) (hj : j ≤ k) :
    prefixCountCanonicalRhoHitNat t w j ↔
      prefixCountCanonicalRhoHitNat t v j :=
  prefixCountCanonicalRhoHitNat_congr
    (fun hjlt => h ⟨j, hjlt⟩ hj)

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

theorem prefixCountCanonicalRho_pred_hitNat
    {d m : Nat} (hd2 : 2 ≤ d)
    {t : ZMod m} {w : PrefixCountRootState d m}
    (h : (prefixCountCanonicalRho d m hd2 t w).val < d - 1) :
    prefixCountCanonicalRhoHitNat t w
      ((prefixCountCanonicalRho d m hd2 t w).val - 1) := by
  classical
  by_cases hhit : ∃ j : Nat, prefixCountCanonicalRhoHitNat t w j
  · have hspec := prefixCountCanonicalRhoFirstNat_spec hhit
    have hval := prefixCountCanonicalRho_val_eq_find_succ
      (d := d) (m := m) hd2 (t := t) (w := w) hhit
    have hidx :
        prefixCountCanonicalRhoFirstNat t w hhit =
          (prefixCountCanonicalRho d m hd2 t w).val - 1 := by
      omega
    simpa [hidx] using hspec
  · have hlast := prefixCountCanonicalRho_eq_last_of_no_hit
      (d := d) (m := m) hd2 (t := t) (w := w) hhit
    have hval :
        (prefixCountCanonicalRho d m hd2 t w).val = d - 1 :=
      congrArg Fin.val hlast
    omega

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

theorem prefixCountCanonicalRho_val_lt_succ_iff_exists_hit_before
    {d m : Nat} (hd2 : 2 ≤ d)
    {t : ZMod m} {w : PrefixCountRootState d m}
    {l : Nat} (hl : l < d - 1) :
    (prefixCountCanonicalRho d m hd2 t w).val < l + 1 ↔
      ∃ j : Nat, j < l ∧ prefixCountCanonicalRhoHitNat t w j := by
  constructor
  · intro hrho_lt
    have hrho_tail :
        (prefixCountCanonicalRho d m hd2 t w).val < d - 1 := by
      omega
    have hhit :=
      prefixCountCanonicalRho_pred_hitNat
        (d := d) (m := m) hd2 (t := t) (w := w) hrho_tail
    refine ⟨(prefixCountCanonicalRho d m hd2 t w).val - 1, ?_, hhit⟩
    have hnonzero :
        (prefixCountCanonicalRho d m hd2 t w).val ≠ 0 :=
      prefixCountCanonicalRho_ne_zero hd2 t w
    omega
  · intro hex
    rcases hex with ⟨j, hjlt, hhit⟩
    by_cases h : ∃ q : Nat, prefixCountCanonicalRhoHitNat t w q
    · have hmin := prefixCountCanonicalRho_minimal hd2 h hhit
      omega
    · exact False.elim (h ⟨j, hhit⟩)

theorem prefixCountCanonicalRho_val_eq_succ_iff_hit_and_no_hit_before
    {d m : Nat} (hd2 : 2 ≤ d)
    {t : ZMod m} {w : PrefixCountRootState d m}
    {k : Nat} (hk : k < d - 2) :
    (prefixCountCanonicalRho d m hd2 t w).val = k + 1 ↔
      prefixCountCanonicalRhoHitNat t w k ∧
        ∀ j : Nat, j < k → ¬ prefixCountCanonicalRhoHitNat t w j := by
  constructor
  · intro hrho
    have htail :
        (prefixCountCanonicalRho d m hd2 t w).val < d - 1 := by
      omega
    have hhit :
        prefixCountCanonicalRhoHitNat t w k := by
      have hpred :=
        prefixCountCanonicalRho_pred_hitNat
          (d := d) (m := m) hd2 (t := t) (w := w) htail
      have hidx :
          (prefixCountCanonicalRho d m hd2 t w).val - 1 = k := by
        omega
      simpa [hidx] using hpred
    refine ⟨hhit, ?_⟩
    intro j hjlt hhitj
    have hmin :
        (prefixCountCanonicalRho d m hd2 t w).val ≤ j + 1 := by
      exact prefixCountCanonicalRho_minimal
        (d := d) (m := m) hd2
        (t := t) (w := w) ⟨k, hhit⟩ hhitj
    omega
  · intro hdata
    rcases hdata with ⟨hhit, hno⟩
    have hle :
        (prefixCountCanonicalRho d m hd2 t w).val ≤ k + 1 := by
      exact prefixCountCanonicalRho_minimal
        (d := d) (m := m) hd2
        (t := t) (w := w) ⟨k, hhit⟩ hhit
    have hnotlt :
        ¬ (prefixCountCanonicalRho d m hd2 t w).val < k + 1 := by
      intro hlt
      rcases
        (prefixCountCanonicalRho_val_lt_succ_iff_exists_hit_before
          (d := d) (m := m) hd2 (t := t) (w := w)
          (l := k) (by omega)).1 hlt with
        ⟨j, hjlt, hhitj⟩
      exact hno j hjlt hhitj
    omega

theorem prefixCountCanonicalRho_not_lt_succ_succ_iff_no_hit_upto
    {d m : Nat} (hd2 : 2 ≤ d)
    {t : ZMod m} {w : PrefixCountRootState d m}
    {k : Nat} (hk : k < d - 2) :
    ¬ (prefixCountCanonicalRho d m hd2 t w).val < k + 2 ↔
      ∀ j : Nat, j ≤ k → ¬ prefixCountCanonicalRhoHitNat t w j := by
  constructor
  · intro hnot j hj hhit
    apply hnot
    have hle :
        (prefixCountCanonicalRho d m hd2 t w).val ≤ j + 1 := by
      exact prefixCountCanonicalRho_minimal
        (d := d) (m := m) hd2
        (t := t) (w := w) ⟨j, hhit⟩ hhit
    omega
  · intro hno hlt
    rcases
      (prefixCountCanonicalRho_val_lt_succ_iff_exists_hit_before
        (d := d) (m := m) hd2 (t := t) (w := w)
        (l := k + 1) (by omega)).1 hlt with
      ⟨j, hjlt, hhitj⟩
    exact hno j (by omega) hhitj

theorem prefixCountCanonicalRho_val_lt_succ_congr_of_agreeUpTo
    {d m : Nat} (hd2 : 2 ≤ d)
    {t : ZMod m} {w v : PrefixCountRootState d m}
    {K l : Nat} (h : prefixCountRootAgreeUpTo K w v)
    (hKl : l ≤ K + 1) (hl : l < d - 1) :
    (prefixCountCanonicalRho d m hd2 t w).val < l + 1 ↔
      (prefixCountCanonicalRho d m hd2 t v).val < l + 1 := by
  constructor
  · intro hw
    rcases
      (prefixCountCanonicalRho_val_lt_succ_iff_exists_hit_before
        (d := d) (m := m) hd2 (t := t) (w := w) (l := l) hl).1 hw with
      ⟨j, hjlt, hhit⟩
    have hjK : j ≤ K := by omega
    exact
      (prefixCountCanonicalRho_val_lt_succ_iff_exists_hit_before
        (d := d) (m := m) hd2 (t := t) (w := v) (l := l) hl).2
        ⟨j, hjlt,
          (prefixCountCanonicalRhoHitNat_congr_of_agreeUpTo
            (d := d) (m := m) (t := t) (w := w) (v := v)
            h hjK).1 hhit⟩
  · intro hv
    rcases
      (prefixCountCanonicalRho_val_lt_succ_iff_exists_hit_before
        (d := d) (m := m) hd2 (t := t) (w := v) (l := l) hl).1 hv with
      ⟨j, hjlt, hhit⟩
    have hjK : j ≤ K := by omega
    exact
      (prefixCountCanonicalRho_val_lt_succ_iff_exists_hit_before
        (d := d) (m := m) hd2 (t := t) (w := w) (l := l) hl).2
        ⟨j, hjlt,
          (prefixCountCanonicalRhoHitNat_congr_of_agreeUpTo
            (d := d) (m := m) (t := t) (w := w) (v := v)
            h hjK).2 hhit⟩

theorem prefixCountCanonicalRho_val_eq_succ_congr_of_agreeUpTo
    {d m : Nat} (hd2 : 2 ≤ d)
    {t : ZMod m} {w v : PrefixCountRootState d m}
    {k : Nat} (hk : k < d - 2)
    (h : prefixCountRootAgreeUpTo k w v) :
    (prefixCountCanonicalRho d m hd2 t w).val = k + 1 ↔
      (prefixCountCanonicalRho d m hd2 t v).val = k + 1 := by
  constructor
  · intro hw
    rcases
      (prefixCountCanonicalRho_val_eq_succ_iff_hit_and_no_hit_before
        (d := d) (m := m) hd2 (t := t) (w := w) (k := k) hk).1 hw with
      ⟨hhit, hno⟩
    exact
      (prefixCountCanonicalRho_val_eq_succ_iff_hit_and_no_hit_before
        (d := d) (m := m) hd2 (t := t) (w := v) (k := k) hk).2
        ⟨(prefixCountCanonicalRhoHitNat_congr_of_agreeUpTo
            (d := d) (m := m) (t := t) (w := w) (v := v)
            h (Nat.le_refl k)).1 hhit,
          by
            intro j hj hhitv
            exact hno j hj
              ((prefixCountCanonicalRhoHitNat_congr_of_agreeUpTo
                (d := d) (m := m) (t := t) (w := w) (v := v)
                h (by omega)).2 hhitv)⟩
  · intro hv
    rcases
      (prefixCountCanonicalRho_val_eq_succ_iff_hit_and_no_hit_before
        (d := d) (m := m) hd2 (t := t) (w := v) (k := k) hk).1 hv with
      ⟨hhit, hno⟩
    exact
      (prefixCountCanonicalRho_val_eq_succ_iff_hit_and_no_hit_before
        (d := d) (m := m) hd2 (t := t) (w := w) (k := k) hk).2
        ⟨(prefixCountCanonicalRhoHitNat_congr_of_agreeUpTo
            (d := d) (m := m) (t := t) (w := w) (v := v)
            h (Nat.le_refl k)).2 hhit,
          by
            intro j hj hhitw
            exact hno j hj
              ((prefixCountCanonicalRhoHitNat_congr_of_agreeUpTo
                (d := d) (m := m) (t := t) (w := w) (v := v)
                h (by omega)).1 hhitw)⟩

theorem prefixCountCanonicalRho_not_lt_succ_succ_congr_of_agreeUpTo
    {d m : Nat} (hd2 : 2 ≤ d)
    {t : ZMod m} {w v : PrefixCountRootState d m}
    {k : Nat} (hk : k < d - 2)
    (h : prefixCountRootAgreeUpTo k w v) :
    (¬ (prefixCountCanonicalRho d m hd2 t w).val < k + 2) ↔
      ¬ (prefixCountCanonicalRho d m hd2 t v).val < k + 2 := by
  constructor
  · intro hw hv
    exact hw
      ((prefixCountCanonicalRho_val_lt_succ_congr_of_agreeUpTo
        (d := d) (m := m) hd2 (t := t) (w := w) (v := v)
        (K := k) (l := k + 1) h (by omega) (by omega)).2 hv)
  · intro hv hw
    exact hv
      ((prefixCountCanonicalRho_val_lt_succ_congr_of_agreeUpTo
        (d := d) (m := m) hd2 (t := t) (w := w) (v := v)
        (K := k) (l := k + 1) h (by omega) (by omega)).1 hw)

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

theorem prefixCountFirstHitReturnBaseStep_sum_fin_iterate
    {d m : Nat} [NeZero m] {C : PrefixCount.Parts d}
    (hC : C.Admissible m) (c : Fin d)
    {α : Type*} [AddCommMonoid α] (F : ZMod m → α) :
    (∑ u : Fin m,
      F (((prefixCountFirstHitReturnBaseStep (m := m) C c)^[u.val])
        (0 : ZMod m))) =
      ∑ z : ZMod m, F z := by
  classical
  let orbit : Fin m → ZMod m := fun u =>
    ((prefixCountFirstHitReturnBaseStep (m := m) C c)^[u.val])
      (0 : ZMod m)
  have hsurj : Function.Surjective orbit := by
    intro z
    rcases prefixCountFirstHitReturnBaseStep_cover
        (m := m) hC c (0 : ZMod m) z with
      ⟨k, hk, hz⟩
    exact ⟨⟨k, hk⟩, by simpa [orbit] using hz⟩
  have hbij : Function.Bijective orbit := by
    have hcard : Fintype.card (Fin m) = Fintype.card (ZMod m) := by
      simp [ZMod.card]
    exact
      (Fintype.bijective_iff_surjective_and_card orbit).2
        ⟨hsurj, hcard⟩
  let e : Fin m ≃ ZMod m := Equiv.ofBijective orbit hbij
  calc
    (∑ u : Fin m,
      F (((prefixCountFirstHitReturnBaseStep (m := m) C c)^[u.val])
        (0 : ZMod m)))
        = ∑ u : Fin m, F (e u) := by
          rfl
    _ = ∑ z : ZMod m, F z := by
          exact Fintype.sum_equiv e (fun u => F (e u)) F (by intro u; rfl)

theorem prefixCountFirstHitReturnBaseStep_sum_range_iterate
    {d m : Nat} [NeZero m] {C : PrefixCount.Parts d}
    (hC : C.Admissible m) (c : Fin d)
    {α : Type*} [AddCommMonoid α] (F : ZMod m → α) :
    (∑ u ∈ Finset.range m,
      F (((prefixCountFirstHitReturnBaseStep (m := m) C c)^[u])
        (0 : ZMod m))) =
      ∑ z : ZMod m, F z := by
  rw [Finset.sum_range]
  exact prefixCountFirstHitReturnBaseStep_sum_fin_iterate
    (m := m) hC c F

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
  classical
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
  · rw [if_pos h]
    rw [if_pos (by simpa [rho, s] using hiff.mp h)]
  · rw [if_neg h]
    rw [if_neg (by
      intro hcase
      have hcase' :
          (s.val = 1 ∧ rho.val = j.val + 1) ∨
            (s.val = j.val + 1 ∧ 1 < s.val ∧ rho.val < s.val) ∨
            (s.val = j.val + 2 ∧ ¬ rho.val < s.val) := by
        simpa [rho, s] using hcase
      exact h (hiff.mpr hcase'))]

def prefixCountFirstHitReturnFiberHitCondition
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    (z : ZMod m) (tail : Fin (d - 2) → ZMod m)
    (j : Fin (d - 2)) (t : Nat) : Prop :=
  let rho :=
    prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m)
      ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t
        ((prefixCountRootStateHeadTailEquiv d m hd2).symm
          (z, tail)))
  let s := L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c
  (s.val = 1 ∧ rho.val = j.val + 1) ∨
    (s.val = j.val + 1 ∧ 1 < s.val ∧ rho.val < s.val) ∨
    (s.val = j.val + 2 ∧ ¬ rho.val < s.val)

noncomputable instance prefixCountFirstHitReturnFiberHitCondition_decidable
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    (z : ZMod m) (tail : Fin (d - 2) → ZMod m)
    (j : Fin (d - 2)) (t : Nat) :
    Decidable
      (prefixCountFirstHitReturnFiberHitCondition hd2 L c z tail j t) := by
  unfold prefixCountFirstHitReturnFiberHitCondition
  infer_instance

def prefixCountFirstHitReturnFiberHitConditionAt
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    (w : PrefixCountRootState d m) (j : Fin (d - 2)) (t : Nat) : Prop :=
  let rho := prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m) w
  let s := L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c
  (s.val = 1 ∧ rho.val = j.val + 1) ∨
    (s.val = j.val + 1 ∧ 1 < s.val ∧ rho.val < s.val) ∨
    (s.val = j.val + 2 ∧ ¬ rho.val < s.val)

theorem prefixCountFirstHitReturnFiberHitCondition_eq_at
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    (z : ZMod m) (tail : Fin (d - 2) → ZMod m)
    (j : Fin (d - 2)) (t : Nat) :
    prefixCountFirstHitReturnFiberHitCondition hd2 L c z tail j t =
      prefixCountFirstHitReturnFiberHitConditionAt hd2 L c
        ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t
        ((prefixCountRootStateHeadTailEquiv d m hd2).symm
            (z, tail)))
        j t := rfl

theorem prefixCountFirstHitReturnFiberHitConditionAt_iff_lambda
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    (w : PrefixCountRootState d m) (j : Fin (d - 2)) (t : Nat) :
    prefixCountFirstHitReturnFiberHitConditionAt hd2 L c w j t ↔
      (prefixCountLambdaRho d
        (prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m) w)
        (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c)).val =
          j.val + 1 := by
  let rho := prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m) w
  let s := L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c
  have hiff :
      (prefixCountLambdaRho d rho s).val = j.val + 1 ↔
        (s.val = 1 ∧ rho.val = j.val + 1) ∨
          (s.val = j.val + 1 ∧ 1 < s.val ∧ rho.val < s.val) ∨
          (s.val = j.val + 2 ∧ ¬ rho.val < s.val) := by
    simpa [Nat.add_assoc] using
      (prefixCountLambdaRho_val_eq_pos_iff
        (d := d) rho s (l := j.val + 1) (Nat.succ_pos j.val))
  simpa [prefixCountFirstHitReturnFiberHitConditionAt, rho, s] using hiff.symm

theorem prefixCountFirstHitReturnFiberHitConditionAt_congr_of_agreeUpTo
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    {w v : PrefixCountRootState d m} (j : Fin (d - 2)) (t : Nat)
    (h : prefixCountRootAgreeUpTo j.val w v) :
    prefixCountFirstHitReturnFiberHitConditionAt hd2 L c w j t ↔
      prefixCountFirstHitReturnFiberHitConditionAt hd2 L c v j t := by
  let rhoW := prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m) w
  let rhoV := prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m) v
  let s := L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c
  have heq :
      rhoW.val = j.val + 1 ↔ rhoV.val = j.val + 1 := by
    simpa [rhoW, rhoV] using
      (prefixCountCanonicalRho_val_eq_succ_congr_of_agreeUpTo
        (d := d) (m := m) hd2
        (t := ((t : Nat) : ZMod m)) (w := w) (v := v)
        (k := j.val) j.isLt h)
  have hlt :
      rhoW.val < j.val + 1 ↔ rhoV.val < j.val + 1 := by
    simpa [rhoW, rhoV] using
      (prefixCountCanonicalRho_val_lt_succ_congr_of_agreeUpTo
        (d := d) (m := m) hd2
        (t := ((t : Nat) : ZMod m)) (w := w) (v := v)
        (K := j.val) (l := j.val) h (by omega) (by omega))
  have hnlt :
      (¬ rhoW.val < j.val + 2) ↔ ¬ rhoV.val < j.val + 2 := by
    simpa [rhoW, rhoV] using
      (prefixCountCanonicalRho_not_lt_succ_succ_congr_of_agreeUpTo
        (d := d) (m := m) hd2
        (t := ((t : Nat) : ZMod m)) (w := w) (v := v)
        (k := j.val) j.isLt h)
  constructor
  · intro hcase
    change
      (s.val = 1 ∧ rhoV.val = j.val + 1) ∨
        (s.val = j.val + 1 ∧ 1 < s.val ∧ rhoV.val < s.val) ∨
        (s.val = j.val + 2 ∧ ¬ rhoV.val < s.val)
    change
      (s.val = 1 ∧ rhoW.val = j.val + 1) ∨
        (s.val = j.val + 1 ∧ 1 < s.val ∧ rhoW.val < s.val) ∨
        (s.val = j.val + 2 ∧ ¬ rhoW.val < s.val) at hcase
    rcases hcase with ⟨hs, hrho⟩ | ⟨hs, hspos, hrho⟩ | ⟨hs, hrho⟩
    · exact Or.inl ⟨hs, heq.mp hrho⟩
    · exact Or.inr (Or.inl ⟨hs, hspos, by
        rw [hs]
        exact hlt.mp (by simpa [hs] using hrho)⟩)
    · exact Or.inr (Or.inr ⟨hs, by
        rw [hs]
        exact hnlt.mp (by simpa [hs] using hrho)⟩)
  · intro hcase
    change
      (s.val = 1 ∧ rhoW.val = j.val + 1) ∨
        (s.val = j.val + 1 ∧ 1 < s.val ∧ rhoW.val < s.val) ∨
        (s.val = j.val + 2 ∧ ¬ rhoW.val < s.val)
    change
      (s.val = 1 ∧ rhoV.val = j.val + 1) ∨
        (s.val = j.val + 1 ∧ 1 < s.val ∧ rhoV.val < s.val) ∨
        (s.val = j.val + 2 ∧ ¬ rhoV.val < s.val) at hcase
    rcases hcase with ⟨hs, hrho⟩ | ⟨hs, hspos, hrho⟩ | ⟨hs, hrho⟩
    · exact Or.inl ⟨hs, heq.mpr hrho⟩
    · exact Or.inr (Or.inl ⟨hs, hspos, by
        rw [hs]
        exact hlt.mpr (by simpa [hs] using hrho)⟩)
    · exact Or.inr (Or.inr ⟨hs, by
        rw [hs]
        exact hnlt.mpr (by simpa [hs] using hrho)⟩)

theorem prefixCountFirstHitCanonicalSchedule_layerMap_nat_agreeUpTo
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    {K : Nat} (hK : K < d - 2) (t : Nat)
    {w v : PrefixCountRootState d m}
    (h : prefixCountRootAgreeUpTo K w v) :
    prefixCountRootAgreeUpTo K
      ((prefixCountFirstHitCanonicalSchedule hd2 L).layerMap
        ((t : Nat) : ZMod m) c w)
      ((prefixCountFirstHitCanonicalSchedule hd2 L).layerMap
        ((t : Nat) : ZMod m) c v) := by
  intro p hp
  let dirW :=
    prefixCountLambdaRho d
      (prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m) w)
      (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c)
  let dirV :=
    prefixCountLambdaRho d
      (prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m) v)
      (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c)
  have hbase : w p = v p := h p hp
  have hdir :
      (dirW.val = p.val) ↔ (dirV.val = p.val) := by
    by_cases hp0 : p.val = 0
    · have hW0 :
          dirW.val = 0 ↔
            (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c).val = 0 := by
        simpa [dirW] using
          (prefixCountLambdaRho_val_eq_zero_iff
            (d := d)
            (prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m) w)
            (s := L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c)
            (prefixCountCanonicalRho_ne_zero hd2 ((t : Nat) : ZMod m) w))
      have hV0 :
          dirV.val = 0 ↔
            (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c).val = 0 := by
        simpa [dirV] using
          (prefixCountLambdaRho_val_eq_zero_iff
            (d := d)
            (prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m) v)
            (s := L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c)
            (prefixCountCanonicalRho_ne_zero hd2 ((t : Nat) : ZMod m) v))
      simpa [hp0] using hW0.trans hV0.symm
    · let q : Fin (d - 2) := ⟨p.val - 1, by omega⟩
      have hpq : p.val = q.val + 1 := by
        simp [q]
        omega
      have hqK : q.val ≤ K := by
        simp [q]
        omega
      have hq :
          prefixCountRootAgreeUpTo q.val w v :=
        prefixCountRootAgreeUpTo_mono hqK h
      have hhit :=
        prefixCountFirstHitReturnFiberHitConditionAt_congr_of_agreeUpTo
          (d := d) (m := m) hd2 L c q t hq
      have hiffW :=
        prefixCountFirstHitReturnFiberHitConditionAt_iff_lambda
          (d := d) (m := m) hd2 L c w q t
      have hiffV :=
        prefixCountFirstHitReturnFiberHitConditionAt_iff_lambda
          (d := d) (m := m) hd2 L c v q t
      calc
        dirW.val = p.val
            ↔ dirW.val = q.val + 1 := by rw [hpq]
        _ ↔ prefixCountFirstHitReturnFiberHitConditionAt hd2 L c w q t :=
            hiffW.symm
        _ ↔ prefixCountFirstHitReturnFiberHitConditionAt hd2 L c v q t :=
            hhit
        _ ↔ dirV.val = q.val + 1 :=
            hiffV
        _ ↔ dirV.val = p.val := by rw [hpq]
  unfold Shared.RootFlatSchedule.layerMap prefixCountFirstHitCanonicalSchedule
    prefixCountCanonicalSchedule prefixCountCanonicalDir
  simp only
  rw [prefixCountRootStep_apply_coord, prefixCountRootStep_apply_coord]
  by_cases hW : dirW.val = p.val
  · have hV : dirV.val = p.val := hdir.mp hW
    simp [dirW, dirV, hW, hV, hbase]
  · have hV : ¬ dirV.val = p.val := by
      intro hV
      exact hW (hdir.mpr hV)
    simp [dirW, dirV, hW, hV, hbase]

theorem prefixCountFirstHitCanonicalSchedule_prefixMap_agreeUpTo
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    {K : Nat} (hK : K < d - 2) :
    ∀ n : Nat, ∀ {w v : PrefixCountRootState d m},
      prefixCountRootAgreeUpTo K w v →
        prefixCountRootAgreeUpTo K
          ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c n w)
          ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c n v)
  | 0, w, v, h => h
  | n + 1, w, v, h => by
      rw [Shared.RootFlatSchedule.prefixMap]
      exact prefixCountFirstHitCanonicalSchedule_layerMap_nat_agreeUpTo
        (d := d) (m := m) hd2 L c hK n
        (prefixCountFirstHitCanonicalSchedule_prefixMap_agreeUpTo
          (d := d) (m := m) hd2 L c hK n h)

theorem prefixCountFirstHitReturnFiberStep_apply_hitCondition
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    (z : ZMod m) (tail : Fin (d - 2) → ZMod m) (j : Fin (d - 2)) :
    prefixCountFirstHitReturnFiberStep hd2 L c z tail j =
      tail j +
        ∑ t ∈ Finset.range m,
          if prefixCountFirstHitReturnFiberHitCondition hd2 L c z tail j t
          then (1 : ZMod m) else 0 := by
  classical
  rw [prefixCountFirstHitReturnFiberStep_apply_cases]
  rfl

theorem prefixCountFirstHitReturnFiberStep_increment_eq_hitCondition_sum
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    (z : ZMod m) (tail : Fin (d - 2) → ZMod m) (j : Fin (d - 2)) :
    prefixCountFirstHitReturnFiberStep hd2 L c z tail j - tail j =
      ∑ t ∈ Finset.range m,
        if prefixCountFirstHitReturnFiberHitCondition hd2 L c z tail j t
        then (1 : ZMod m) else 0 := by
  rw [prefixCountFirstHitReturnFiberStep_apply_hitCondition]
  abel

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
      Nonempty
        (Shared.CycleCoordinate (m ^ (d - 2))
          (prefixCountFirstHitReturnTailMonodromy hd2 L c))

noncomputable def prefixCountFirstHitReturnTailCocycle
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) (k : Nat) (hk : k < d - 2) :
    (Fin k → ZMod m) → ZMod m :=
  fun x =>
    prefixCountFirstHitReturnTailMonodromy hd2 L c
      (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x) ⟨k, hk⟩

theorem prefixCountFirstHitReturnTailCocycle_eq_monodromy_increment
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) (k : Nat) (hk : k < d - 2)
    (x : Fin k → ZMod m) :
    prefixCountFirstHitReturnTailCocycle hd2 L c k hk x =
      prefixCountFirstHitReturnTailMonodromy hd2 L c
          (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x) ⟨k, hk⟩ -
        Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x ⟨k, hk⟩ := by
  simp [prefixCountFirstHitReturnTailCocycle]

theorem prefixCountFirstHitReturnTailCocycle_eq_fiberIterate
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) (k : Nat) (hk : k < d - 2)
    (x : Fin k → ZMod m) :
    prefixCountFirstHitReturnTailCocycle hd2 L c k hk x =
      Shared.skewFiberIterate
        (prefixCountFirstHitReturnBaseStep (m := m) C c)
        (prefixCountFirstHitReturnFiberStep hd2 L c)
        m (0 : ZMod m)
        (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x) ⟨k, hk⟩ := by
  unfold prefixCountFirstHitReturnTailCocycle
  rw [prefixCountFirstHitReturnTailMonodromy_apply_eq_fiberIterate]

theorem prefixCountFirstHitReturnTailCocycle_eq_sum_fiberStep_increment
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) (k : Nat) (hk : k < d - 2)
    (x : Fin k → ZMod m) :
    prefixCountFirstHitReturnTailCocycle hd2 L c k hk x =
      ∑ u ∈ Finset.range m,
        (prefixCountFirstHitReturnFiberStep hd2 L c
            (((prefixCountFirstHitReturnBaseStep (m := m) C c)^[u])
              (0 : ZMod m))
            (Shared.skewFiberIterate
              (prefixCountFirstHitReturnBaseStep (m := m) C c)
              (prefixCountFirstHitReturnFiberStep hd2 L c)
              u (0 : ZMod m)
              (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x))
            ⟨k, hk⟩ -
          Shared.skewFiberIterate
              (prefixCountFirstHitReturnBaseStep (m := m) C c)
              (prefixCountFirstHitReturnFiberStep hd2 L c)
              u (0 : ZMod m)
              (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x) ⟨k, hk⟩) := by
  let baseStep := prefixCountFirstHitReturnBaseStep (m := m) C c
  let fiberStep := prefixCountFirstHitReturnFiberStep hd2 L c
  let tail0 := Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x
  let j : Fin (d - 2) := ⟨k, hk⟩
  rw [prefixCountFirstHitReturnTailCocycle_eq_fiberIterate
    (hd2 := hd2) (C := C) L c k hk x]
  have hgen :=
    Shared.skewFiberIterate_coord_eq_add_sum_range
      baseStep fiberStep
      (fun z tail => fiberStep z tail j - tail j) j
      (by
        intro z tail
        simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm])
      m (0 : ZMod m) tail0
  have hzero : tail0 j = 0 := by
    simp [tail0, j]
  rw [hgen, hzero, zero_add]

theorem prefixCountFirstHitReturnTailCocycle_eq_sum_hitCondition
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) (k : Nat) (hk : k < d - 2)
    (x : Fin k → ZMod m) :
    prefixCountFirstHitReturnTailCocycle hd2 L c k hk x =
      ∑ u ∈ Finset.range m,
        ∑ t ∈ Finset.range m,
          if prefixCountFirstHitReturnFiberHitCondition hd2 L c
              (((prefixCountFirstHitReturnBaseStep (m := m) C c)^[u])
                (0 : ZMod m))
              (Shared.skewFiberIterate
                (prefixCountFirstHitReturnBaseStep (m := m) C c)
                (prefixCountFirstHitReturnFiberStep hd2 L c)
                u (0 : ZMod m)
                (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x))
              ⟨k, hk⟩ t
          then (1 : ZMod m) else 0 := by
  rw [prefixCountFirstHitReturnTailCocycle_eq_sum_fiberStep_increment
    (hd2 := hd2) (C := C) L c k hk x]
  apply Finset.sum_congr rfl
  intro u _hu
  rw [prefixCountFirstHitReturnFiberStep_increment_eq_hitCondition_sum]

def PrefixCountFirstHitReturnTailIncrementDependsOnTakeGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) →
    ∀ c : Fin d, ∀ tail : Fin (d - 2) → ZMod m,
      ∀ k : Nat, ∀ hk : k < d - 2,
        prefixCountFirstHitReturnTailMonodromy hd2 L c tail ⟨k, hk⟩ -
            tail ⟨k, hk⟩ =
          prefixCountFirstHitReturnTailCocycle hd2 L c k hk
            (Shared.zmodVectorTake (Nat.le_of_lt hk) tail)

def PrefixCountFirstHitReturnFiberIncrementDependsOnTakeGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) →
    ∀ c : Fin d, ∀ z : ZMod m,
      Shared.ZModVectorIncrementDependsOnTake
        (prefixCountFirstHitReturnFiberStep hd2 L c z)

def PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) →
    ∀ c : Fin d, ∀ z : ZMod m,
      ∀ x y : Fin (d - 2) → ZMod m, ∀ k : Nat, ∀ hk : k < d - 2,
        Shared.zmodVectorTake (Nat.le_of_lt hk) x =
          Shared.zmodVectorTake (Nat.le_of_lt hk) y →
        ∀ t ∈ Finset.range m,
          prefixCountFirstHitReturnFiberHitCondition hd2 L c z x ⟨k, hk⟩ t ↔
            prefixCountFirstHitReturnFiberHitCondition hd2 L c z y ⟨k, hk⟩ t

def PrefixCountFirstHitReturnTailTriangularGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) →
    ∀ c : Fin d, ∀ tail : Fin (d - 2) → ZMod m,
      ∀ k : Nat, ∀ hk : k < d - 2,
        prefixCountFirstHitReturnTailMonodromy hd2 L c tail ⟨k, hk⟩ =
          tail ⟨k, hk⟩ +
            prefixCountFirstHitReturnTailCocycle hd2 L c k hk
              (Shared.zmodVectorTake (Nat.le_of_lt hk) tail)

def PrefixCountFirstHitReturnTailCocycleUnitGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) →
    ∀ c : Fin d, ∀ k : Nat, ∀ hk : k < d - 2,
      IsUnit
        (∑ x : (Fin k → ZMod m),
          prefixCountFirstHitReturnTailCocycle hd2 L c k hk x)

def PrefixCountFirstHitReturnTailCocycleSumGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) →
    ∀ c : Fin d, ∀ k : Nat, ∀ hk : k < d - 2,
      (∑ x : (Fin k → ZMod m),
        prefixCountFirstHitReturnTailCocycle hd2 L c k hk x) =
        ((-1 : ZMod m) ^ (k + 1)) *
          (((C.step c ⟨k, hk⟩ : Int) - (C.delta c : Int)) : ZMod m)

def PrefixCountFirstHitReturnTailLocalHitConditionSumGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) →
    ∀ c : Fin d, ∀ k : Nat, ∀ hk : k < d - 2,
      ∀ t ∈ Finset.range m,
        (∑ x : (Fin k → ZMod m),
          ∑ u ∈ Finset.range m,
            if prefixCountFirstHitReturnFiberHitCondition hd2 L c
                (((prefixCountFirstHitReturnBaseStep (m := m) C c)^[u])
                  (0 : ZMod m))
                (Shared.skewFiberIterate
                  (prefixCountFirstHitReturnBaseStep (m := m) C c)
                  (prefixCountFirstHitReturnFiberStep hd2 L c)
                  u (0 : ZMod m)
                  (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x))
                ⟨k, hk⟩ t
            then (1 : ZMod m) else 0) =
          prefixCountReturnTailSignedCoeff hd2 hk
            (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c)

noncomputable def prefixCountFirstHitReturnLowResidualState
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) {k : Nat} (hk : k < d - 2)
    (t u : Nat) (x : Fin k → ZMod m) :
    PrefixCountRootState d m :=
  (prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t
    ((prefixCountRootStateHeadTailEquiv d m hd2).symm
      ((((prefixCountFirstHitReturnBaseStep (m := m) C c)^[u])
          (0 : ZMod m)),
        Shared.skewFiberIterate
          (prefixCountFirstHitReturnBaseStep (m := m) C c)
          (prefixCountFirstHitReturnFiberStep hd2 L c)
          u (0 : ZMod m)
          (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x)))

noncomputable def prefixCountFirstHitLowResidualFromHeadTail
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) {k : Nat} (hk : k < d - 2)
    (t : Nat) (z : ZMod m) (tail : Fin (d - 2) → ZMod m) :
    Fin (k + 1) → ZMod m :=
  fun r =>
    ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t
      ((prefixCountRootStateHeadTailEquiv d m hd2).symm (z, tail)))
      ⟨r.val, by omega⟩ - ((t : Nat) : ZMod m)

theorem prefixCountFirstHitLowResidualFromHeadTail_eq_lowPrefix
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) {k : Nat} (hk : k < d - 2)
    (t : Nat) (z : ZMod m) (tail : Fin (d - 2) → ZMod m)
    (y : Fin k → ZMod m)
    (hTake : Shared.zmodVectorTake (Nat.le_of_lt hk) tail = y) :
    prefixCountFirstHitLowResidualFromHeadTail hd2 L c hk t z tail =
      fun r =>
        Shared.zmodVectorTake (show k + 1 ≤ d - 1 by omega)
          ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t
            (Shared.zmodVectorExtendZero
              (show k + 1 ≤ d - 1 by omega)
              (Fin.cons z y))) r -
          ((t : Nat) : ZMod m) := by
  funext r
  have hAgree :
      prefixCountRootAgreeUpTo k
        ((prefixCountRootStateHeadTailEquiv d m hd2).symm (z, tail))
        (Shared.zmodVectorExtendZero
          (show k + 1 ≤ d - 1 by omega) (Fin.cons z y)) := by
    intro j hj
    by_cases hj0 : j.val = 0
    · have hj' : j = ⟨0, by omega⟩ := Fin.ext hj0
      rw [hj']
      simp [Shared.zmodVectorExtendZero]
    · have hjpred : j.val - 1 < k := by omega
      have htail := congrFun hTake ⟨j.val - 1, hjpred⟩
      have htail' :
          tail ⟨j.val - 1, by omega⟩ =
            y ⟨j.val - 1, hjpred⟩ := by
        simpa [Shared.zmodVectorTake] using htail
      have hidx :
          (⟨(j.val - 1) + 1, by omega⟩ : Fin (d - 1)) = j := by
        apply Fin.ext
        simp
        omega
      rw [← hidx]
      change tail ⟨j.val - 1, by omega⟩ =
        Shared.zmodVectorExtendZero
          (show k + 1 ≤ d - 1 by omega) (Fin.cons z y)
          ⟨(j.val - 1) + 1, by omega⟩
      have hlt :
          (⟨(j.val - 1) + 1, by omega⟩ : Fin (d - 1)).val < k + 1 := by
        simp
        omega
      unfold Shared.zmodVectorExtendZero
      rw [dif_pos hlt]
      have hfin :
          (⟨(j.val - 1) + 1, hlt⟩ : Fin (k + 1)) =
            (⟨j.val - 1, hjpred⟩ : Fin k).succ := by
        apply Fin.ext
        simp
      rw [hfin]
      exact htail'
  have hOut :=
    prefixCountFirstHitCanonicalSchedule_prefixMap_agreeUpTo
      (d := d) (m := m) hd2 L c hk t hAgree
  have hle : k + 1 ≤ d - 1 := by omega
  have hcoord :=
    hOut ⟨r.val, lt_of_lt_of_le r.isLt hle⟩
      (Nat.le_of_lt_succ r.isLt)
  simp [prefixCountFirstHitLowResidualFromHeadTail,
    Shared.zmodVectorTake, hcoord]

noncomputable def prefixCountFirstHitReturnLowResidual
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) {k : Nat} (hk : k < d - 2)
    (t u : Nat) (x : Fin k → ZMod m) :
    Fin (k + 1) → ZMod m :=
  fun r =>
    prefixCountFirstHitReturnLowResidualState hd2 L c hk t u x
      ⟨r.val, by omega⟩ - ((t : Nat) : ZMod m)

theorem prefixCountFirstHitReturnLowResidual_eq_zero_iff_hitNat
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) {k : Nat} (hk : k < d - 2)
    (t u : Nat) (x : Fin k → ZMod m) (r : Fin (k + 1)) :
    prefixCountFirstHitReturnLowResidual hd2 L c hk t u x r = 0 ↔
      prefixCountCanonicalRhoHitNat ((t : Nat) : ZMod m)
        (prefixCountFirstHitReturnLowResidualState hd2 L c hk t u x)
        r.val := by
  constructor
  · intro hzero
    refine ⟨by omega, by omega, ?_⟩
    have hsub :
        prefixCountFirstHitReturnLowResidualState hd2 L c hk t u x
          ⟨r.val, by omega⟩ -
            ((t : Nat) : ZMod m) = 0 := by
      simpa [prefixCountFirstHitReturnLowResidual] using hzero
    exact sub_eq_zero.mp hsub
  · intro hhit
    rcases hhit with ⟨_hr, _hnext, hcoord⟩
    simp [prefixCountFirstHitReturnLowResidual, hcoord]

theorem prefixCountFirstHitReturnLowResidual_exactLastZero_iff_rho_eq
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) {k : Nat} (hk : k < d - 2)
    (t u : Nat) (x : Fin k → ZMod m) :
    prefixCountPcExactLastZero
        (prefixCountFirstHitReturnLowResidual hd2 L c hk t u x) ↔
      (prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m)
        (prefixCountFirstHitReturnLowResidualState hd2 L c hk t u x)).val =
        k + 1 := by
  constructor
  · intro h
    apply
      (prefixCountCanonicalRho_val_eq_succ_iff_hit_and_no_hit_before
        (d := d) (m := m) hd2
        (t := ((t : Nat) : ZMod m))
        (w := prefixCountFirstHitReturnLowResidualState hd2 L c hk t u x)
        (k := k) hk).2
    constructor
    · have hz := h.2
      have hhit :=
        (prefixCountFirstHitReturnLowResidual_eq_zero_iff_hitNat
          (hd2 := hd2) (C := C) L c hk t u x (Fin.last k)).1 hz
      simpa using hhit
    · intro j hj hhit
      have hz :
          prefixCountFirstHitReturnLowResidual hd2 L c hk t u x
            (Fin.castSucc ⟨j, hj⟩) = 0 := by
        exact
          (prefixCountFirstHitReturnLowResidual_eq_zero_iff_hitNat
            (hd2 := hd2) (C := C) L c hk t u x
            (Fin.castSucc ⟨j, hj⟩)).2 (by simpa using hhit)
      exact h.1 ⟨j, hj⟩ hz
  · intro hrho
    have hdata :=
      (prefixCountCanonicalRho_val_eq_succ_iff_hit_and_no_hit_before
        (d := d) (m := m) hd2
        (t := ((t : Nat) : ZMod m))
        (w := prefixCountFirstHitReturnLowResidualState hd2 L c hk t u x)
        (k := k) hk).1 hrho
    constructor
    · intro i
      intro hz
      have hhit :=
        (prefixCountFirstHitReturnLowResidual_eq_zero_iff_hitNat
          (hd2 := hd2) (C := C) L c hk t u x i.castSucc).1 hz
      exact hdata.2 i.val i.isLt (by simpa using hhit)
    · exact
        (prefixCountFirstHitReturnLowResidual_eq_zero_iff_hitNat
          (hd2 := hd2) (C := C) L c hk t u x (Fin.last k)).2
          (by simpa using hdata.1)

theorem prefixCountFirstHitReturnLowResidual_hitBeforeLastZero_iff_rho_lt
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) {k : Nat} (hk : k < d - 2)
    (t u : Nat) (x : Fin k → ZMod m) :
    prefixCountPcHitBeforeLastZero
        (prefixCountFirstHitReturnLowResidual hd2 L c hk t u x) ↔
      (prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m)
        (prefixCountFirstHitReturnLowResidualState hd2 L c hk t u x)).val <
        k + 1 := by
  rw [prefixCountCanonicalRho_val_lt_succ_iff_exists_hit_before
    (d := d) (m := m) hd2
    (t := ((t : Nat) : ZMod m))
    (w := prefixCountFirstHitReturnLowResidualState hd2 L c hk t u x)
    (l := k) (by omega)]
  constructor
  · intro h
    rcases h with ⟨i, hi⟩
    refine ⟨i.val, i.isLt, ?_⟩
    exact
      (prefixCountFirstHitReturnLowResidual_eq_zero_iff_hitNat
        (hd2 := hd2) (C := C) L c hk t u x i.castSucc).1 hi
  · intro h
    rcases h with ⟨j, hj, hhit⟩
    refine ⟨⟨j, hj⟩, ?_⟩
    exact
      (prefixCountFirstHitReturnLowResidual_eq_zero_iff_hitNat
        (hd2 := hd2) (C := C) L c hk t u x
        (Fin.castSucc ⟨j, hj⟩)).2 (by simpa using hhit)

theorem prefixCountFirstHitReturnLowResidual_noZero_iff_rho_not_lt
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) {k : Nat} (hk : k < d - 2)
    (t u : Nat) (x : Fin k → ZMod m) :
    prefixCountPcNoZero
        (prefixCountFirstHitReturnLowResidual hd2 L c hk t u x) ↔
      ¬ (prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m)
          (prefixCountFirstHitReturnLowResidualState hd2 L c hk t u x)).val <
        k + 2 := by
  rw [prefixCountCanonicalRho_not_lt_succ_succ_iff_no_hit_upto
    (d := d) (m := m) hd2
    (t := ((t : Nat) : ZMod m))
    (w := prefixCountFirstHitReturnLowResidualState hd2 L c hk t u x)
    (k := k) hk]
  constructor
  · intro h j hj hhit
    have hj' : j < k + 1 := by omega
    have hz :
        prefixCountFirstHitReturnLowResidual hd2 L c hk t u x
          ⟨j, hj'⟩ = 0 :=
      (prefixCountFirstHitReturnLowResidual_eq_zero_iff_hitNat
        (hd2 := hd2) (C := C) L c hk t u x ⟨j, hj'⟩).2 hhit
    exact h ⟨j, hj'⟩ hz
  · intro h r hz
    have hhit :=
      (prefixCountFirstHitReturnLowResidual_eq_zero_iff_hitNat
        (hd2 := hd2) (C := C) L c hk t u x r).1 hz
    exact h r.val (by omega) (by simpa using hhit)

theorem prefixCountFirstHitReturnFiberHitCondition_lowResidual_iff
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) {k : Nat} (hk : k < d - 2)
    (t u : Nat) (x : Fin k → ZMod m) :
    prefixCountFirstHitReturnFiberHitCondition hd2 L c
        (((prefixCountFirstHitReturnBaseStep (m := m) C c)^[u])
          (0 : ZMod m))
        (Shared.skewFiberIterate
          (prefixCountFirstHitReturnBaseStep (m := m) C c)
          (prefixCountFirstHitReturnFiberStep hd2 L c)
          u (0 : ZMod m)
          (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x))
        ⟨k, hk⟩ t ↔
      (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c =
          prefixCountReturnTailDeltaCol hd2 ∧
            prefixCountPcExactLastZero
              (prefixCountFirstHitReturnLowResidual hd2 L c hk t u x)) ∨
        ((L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c).val =
            k + 1 ∧
          1 < (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c).val ∧
            prefixCountPcHitBeforeLastZero
              (prefixCountFirstHitReturnLowResidual hd2 L c hk t u x)) ∨
        (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c =
          prefixCountReturnTailStepCol hd2 hk ∧
            prefixCountPcNoZero
              (prefixCountFirstHitReturnLowResidual hd2 L c hk t u x)) := by
  classical
  let s := L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c
  let rho :=
    prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m)
      (prefixCountFirstHitReturnLowResidualState hd2 L c hk t u x)
  have hDeltaVal : s.val = 1 ↔ s = prefixCountReturnTailDeltaCol hd2 := by
    constructor
    · intro h
      apply Fin.ext
      simpa [prefixCountReturnTailDeltaCol, PrefixCount.Parts.colDelta] using h
    · intro h
      simpa [s, h, prefixCountReturnTailDeltaCol,
        PrefixCount.Parts.colDelta]
  have hStepVal : s.val = k + 2 ↔
      s = prefixCountReturnTailStepCol hd2 hk := by
    constructor
    · intro h
      apply Fin.ext
      simpa [prefixCountReturnTailStepCol, PrefixCount.Parts.colStep] using h
    · intro h
      simpa [s, h, prefixCountReturnTailStepCol,
        PrefixCount.Parts.colStep]
  have hExact :
      prefixCountPcExactLastZero
          (prefixCountFirstHitReturnLowResidual hd2 L c hk t u x) ↔
        rho.val = k + 1 := by
    simpa [rho] using
      prefixCountFirstHitReturnLowResidual_exactLastZero_iff_rho_eq
        (hd2 := hd2) (C := C) L c hk t u x
  have hBefore :
      prefixCountPcHitBeforeLastZero
          (prefixCountFirstHitReturnLowResidual hd2 L c hk t u x) ↔
        rho.val < k + 1 := by
    simpa [rho] using
      prefixCountFirstHitReturnLowResidual_hitBeforeLastZero_iff_rho_lt
        (hd2 := hd2) (C := C) L c hk t u x
  have hNo :
      prefixCountPcNoZero
          (prefixCountFirstHitReturnLowResidual hd2 L c hk t u x) ↔
        ¬ rho.val < k + 2 := by
    simpa [rho] using
      prefixCountFirstHitReturnLowResidual_noZero_iff_rho_not_lt
        (hd2 := hd2) (C := C) L c hk t u x
  change
    ((s.val = 1 ∧ rho.val = k + 1) ∨
      (s.val = k + 1 ∧ 1 < s.val ∧ rho.val < s.val) ∨
      (s.val = k + 2 ∧ ¬ rho.val < s.val)) ↔
    ((s = prefixCountReturnTailDeltaCol hd2 ∧
        prefixCountPcExactLastZero
          (prefixCountFirstHitReturnLowResidual hd2 L c hk t u x)) ∨
      (s.val = k + 1 ∧ 1 < s.val ∧
        prefixCountPcHitBeforeLastZero
          (prefixCountFirstHitReturnLowResidual hd2 L c hk t u x)) ∨
      (s = prefixCountReturnTailStepCol hd2 hk ∧
        prefixCountPcNoZero
          (prefixCountFirstHitReturnLowResidual hd2 L c hk t u x)))
  constructor
  · intro h
    rcases h with h | h | h
    · exact Or.inl ⟨hDeltaVal.mp h.1, hExact.mpr h.2⟩
    · have hlt : rho.val < k + 1 := by
        simpa [h.1] using h.2.2
      exact Or.inr (Or.inl ⟨h.1, h.2.1, hBefore.mpr hlt⟩)
    · have hnlt : ¬ rho.val < k + 2 := by
        simpa [h.1] using h.2
      exact Or.inr (Or.inr ⟨hStepVal.mp h.1, hNo.mpr hnlt⟩)
  · intro h
    rcases h with h | h | h
    · exact Or.inl ⟨hDeltaVal.mpr h.1, hExact.mp h.2⟩
    · have hlt : rho.val < s.val := by
        have := hBefore.mp h.2.2
        simpa [h.1] using this
      exact Or.inr (Or.inl ⟨h.1, h.2.1, hlt⟩)
    · have hnlt : ¬ rho.val < s.val := by
        have := hNo.mp h.2
        simpa [hStepVal.mpr h.1] using this
      exact Or.inr (Or.inr ⟨hStepVal.mpr h.1, hnlt⟩)

def PrefixCountFirstHitReturnLowResidualReindexGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) →
    ∀ c : Fin d, ∀ k : Nat, ∀ hk : k < d - 2,
      ∀ t ∈ Finset.range m,
        ∀ F : (Fin (k + 1) → ZMod m) → ZMod m,
          (∑ x : (Fin k → ZMod m),
            ∑ u ∈ Finset.range m,
              F (prefixCountFirstHitReturnLowResidual hd2 L c hk t u x)) =
            ∑ y : (Fin (k + 1) → ZMod m), F y

def PrefixCountFirstHitReturnTailTriangularUnitBlocksGoal : Prop :=
  Shared.ZModVectorLowerTriangularUnitCycleCoordinateGoal ∧
  PrefixCountFirstHitReturnTailTriangularGoal ∧
  PrefixCountFirstHitReturnTailCocycleUnitGoal

def PrefixCountFirstHitReturnTailTriangularCocycleBlocksGoal : Prop :=
  PrefixCountFirstHitReturnTailTriangularGoal ∧
  PrefixCountFirstHitReturnTailCocycleUnitGoal

def PrefixCountFirstHitReturnTailIncrementUnitBlocksGoal : Prop :=
  PrefixCountFirstHitReturnTailIncrementDependsOnTakeGoal ∧
  PrefixCountFirstHitReturnTailCocycleUnitGoal

def PrefixCountFirstHitReturnFiberIncrementUnitBlocksGoal : Prop :=
  PrefixCountFirstHitReturnFiberIncrementDependsOnTakeGoal ∧
  PrefixCountFirstHitReturnTailCocycleUnitGoal

def PrefixCountFirstHitReturnFiberHitConditionUnitBlocksGoal : Prop :=
  PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal ∧
  PrefixCountFirstHitReturnTailCocycleUnitGoal

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
  rcases hCycle hd2 hdodd hd5 hmodd hdm hC L c with ⟨K⟩
  exact ⟨K.equiv.symm, fun tail => Shared.CycleCoordinate.rank_step K tail⟩

theorem prefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal :
    PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal := by
  intro d m _inst hd2 C _hdodd _hd5 _hmodd _hdm _hC L c z x y k hk hxy t _ht
  let wx : PrefixCountRootState d m :=
    (prefixCountRootStateHeadTailEquiv d m hd2).symm (z, x)
  let wy : PrefixCountRootState d m :=
    (prefixCountRootStateHeadTailEquiv d m hd2).symm (z, y)
  have h0 : prefixCountRootAgreeUpTo k wx wy := by
    simpa [wx, wy] using
      prefixCountRootAgreeUpTo_headTail_symm_of_take
        (d := d) (m := m) hd2 (z := z) (x := x) (y := y) hk hxy
  have htAgree :
      prefixCountRootAgreeUpTo k
        ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t wx)
        ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t wy) :=
    prefixCountFirstHitCanonicalSchedule_prefixMap_agreeUpTo
      (d := d) (m := m) hd2 L c hk t h0
  rw [prefixCountFirstHitReturnFiberHitCondition_eq_at
    (hd2 := hd2) (L := L) (c := c) (z := z) (tail := x)
    (j := ⟨k, hk⟩) (t := t)]
  rw [prefixCountFirstHitReturnFiberHitCondition_eq_at
    (hd2 := hd2) (L := L) (c := c) (z := z) (tail := y)
    (j := ⟨k, hk⟩) (t := t)]
  exact
    prefixCountFirstHitReturnFiberHitConditionAt_congr_of_agreeUpTo
      (d := d) (m := m) hd2 L c
      (w := (prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t wx)
      (v := (prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t wy)
      (j := ⟨k, hk⟩) (t := t) htAgree

theorem prefixCountFirstHitReturnFiberIncrementDependsOnTakeGoal_of_hitCondition
    (hHit : PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal) :
    PrefixCountFirstHitReturnFiberIncrementDependsOnTakeGoal := by
  classical
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L c z x y k hk hxy
  rw [prefixCountFirstHitReturnFiberStep_apply_hitCondition
    (hd2 := hd2) (C := C) L c z x ⟨k, hk⟩]
  rw [prefixCountFirstHitReturnFiberStep_apply_hitCondition
    (hd2 := hd2) (C := C) L c z y ⟨k, hk⟩]
  have hsum :
      (∑ t ∈ Finset.range m,
          if prefixCountFirstHitReturnFiberHitCondition hd2 L c z x ⟨k, hk⟩ t
          then (1 : ZMod m) else 0) =
        ∑ t ∈ Finset.range m,
          if prefixCountFirstHitReturnFiberHitCondition hd2 L c z y ⟨k, hk⟩ t
          then (1 : ZMod m) else 0 := by
    apply Finset.sum_congr rfl
    intro t ht
    have hiff := hHit hd2 hdodd hd5 hmodd hdm hC L c z x y k hk hxy t ht
    by_cases hx :
        prefixCountFirstHitReturnFiberHitCondition hd2 L c z x ⟨k, hk⟩ t
    · have hy : prefixCountFirstHitReturnFiberHitCondition
          hd2 L c z y ⟨k, hk⟩ t := hiff.mp hx
      simp [hx, hy]
    · have hy : ¬ prefixCountFirstHitReturnFiberHitCondition
          hd2 L c z y ⟨k, hk⟩ t := by
        intro hy
        exact hx (hiff.mpr hy)
      simp [hx, hy]
  rw [hsum]
  abel

theorem prefixCountFirstHitSkewFiberIterate_lowPrefix_bijective
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d}
    (hdodd : Odd d) (hd5 : 5 ≤ d) (hmodd : Odd m) (hdm : d ≤ m)
    (hC : C.Admissible m)
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    (u k : Nat) (hk : k < d - 2) :
    Function.Bijective
      (fun x : Fin k → ZMod m =>
        Shared.zmodVectorTake (Nat.le_of_lt hk)
          (Shared.skewFiberIterate
            (prefixCountFirstHitReturnBaseStep (m := m) C c)
            (prefixCountFirstHitReturnFiberStep hd2 L c)
            u (0 : ZMod m)
            (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x))) := by
  let F : (Fin (d - 2) → ZMod m) → (Fin (d - 2) → ZMod m) :=
    Shared.skewFiberIterate
      (prefixCountFirstHitReturnBaseStep (m := m) C c)
      (prefixCountFirstHitReturnFiberStep hd2 L c)
      u (0 : ZMod m)
  have hFiber :
      PrefixCountFirstHitReturnFiberIncrementDependsOnTakeGoal :=
    prefixCountFirstHitReturnFiberIncrementDependsOnTakeGoal_of_hitCondition
      prefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal
  have hInc : Shared.ZModVectorIncrementDependsOnTake F := by
    exact
      Shared.zmodVectorIncrementDependsOnTake_skewFiberIterate
        (prefixCountFirstHitReturnBaseStep (m := m) C c)
        (prefixCountFirstHitReturnFiberStep hd2 L c)
        (fun z => hFiber hd2 hdodd hd5 hmodd hdm hC L c z)
        u (0 : ZMod m)
  have hBij : Function.Bijective F := by
    exact
      Shared.skewFiberIterate_bijective
        (prefixCountFirstHitReturnBaseStep (m := m) C c)
        (prefixCountFirstHitReturnFiberStep hd2 L c)
        (prefixCountFirstHitReturnFiberStep_bijective
          hd2 hdodd hd5 hmodd hdm hC L c)
        u (0 : ZMod m)
  exact
    Shared.zmodVectorTake_extendZero_apply_bijective_of_incrementDependsOnTake
      (Nat.le_of_lt hk) hInc hBij

theorem prefixCountFirstHitCanonicalSchedule_prefixMap_lowPrefix_bijective
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d}
    (hdodd : Odd d) (hd5 : 5 ≤ d) (hmodd : Odd m) (hdm : d ≤ m)
    (hC : C.Admissible m)
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    (t k : Nat) (hk : k < d - 2) :
    Function.Bijective
      (fun y : Fin (k + 1) → ZMod m =>
        Shared.zmodVectorTake (show k + 1 ≤ d - 1 by omega)
          ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t
            (Shared.zmodVectorExtendZero
              (show k + 1 ≤ d - 1 by omega) y))) := by
  let hle : k + 1 ≤ d - 1 := by omega
  refine
    Shared.zmodVectorTake_extendZero_apply_bijective_of_take_preserving
      (m := m) hle ?_ ?_
  · intro x y hxy
    funext i
    have hle : k + 1 ≤ d - 1 := by omega
    have hAgree : prefixCountRootAgreeUpTo k x y := by
      intro j hj
      have hji : j.val < k + 1 := by omega
      have hcoord := congrFun hxy ⟨j.val, hji⟩
      simpa [Shared.zmodVectorTake] using hcoord
    have hOut :=
      prefixCountFirstHitCanonicalSchedule_prefixMap_agreeUpTo
        (d := d) (m := m) hd2 L c hk t hAgree
    exact hOut ⟨i.val, lt_of_lt_of_le i.isLt hle⟩
      (Nat.le_of_lt_succ i.isLt)
  · have hLayer :
        (prefixCountFirstHitCanonicalSchedule hd2 L).layerBijective :=
      prefixCountFirstHitCanonicalLayerBijectiveGoal
        hd2 hdodd hd5 hmodd hdm hC L
    exact Shared.RootFlatSchedule.prefixMap_bijective
      (prefixCountFirstHitCanonicalSchedule hd2 L) hLayer c t

theorem prefixCountFirstHitCanonicalSchedule_prefixMap_lowResidual_bijective
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d}
    (hdodd : Odd d) (hd5 : 5 ≤ d) (hmodd : Odd m) (hdm : d ≤ m)
    (hC : C.Admissible m)
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    (t k : Nat) (hk : k < d - 2) :
    Function.Bijective
      (fun y : Fin (k + 1) → ZMod m =>
        fun r =>
          Shared.zmodVectorTake (show k + 1 ≤ d - 1 by omega)
            ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t
              (Shared.zmodVectorExtendZero
                (show k + 1 ≤ d - 1 by omega) y)) r -
            ((t : Nat) : ZMod m)) := by
  exact
    (Shared.zmodVectorSubConst_bijective
      (n := k + 1) (m := m) ((t : Nat) : ZMod m)).comp
      (prefixCountFirstHitCanonicalSchedule_prefixMap_lowPrefix_bijective
        (hd2 := hd2) (C := C) hdodd hd5 hmodd hdm hC L c t k hk)

theorem prefixCountFirstHitCanonicalSchedule_prefixMap_lowResidual_sum
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d}
    (hdodd : Odd d) (hd5 : 5 ≤ d) (hmodd : Odd m) (hdm : d ≤ m)
    (hC : C.Admissible m)
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    (t k : Nat) (hk : k < d - 2)
    {α : Type*} [AddCommMonoid α] (F : (Fin (k + 1) → ZMod m) → α) :
    (∑ y : Fin (k + 1) → ZMod m,
        F (fun r =>
          Shared.zmodVectorTake (show k + 1 ≤ d - 1 by omega)
            ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t
              (Shared.zmodVectorExtendZero
                (show k + 1 ≤ d - 1 by omega) y)) r -
            ((t : Nat) : ZMod m))) =
      ∑ z : Fin (k + 1) → ZMod m, F z := by
  classical
  let G : (Fin (k + 1) → ZMod m) → (Fin (k + 1) → ZMod m) := fun y =>
    fun r =>
      Shared.zmodVectorTake (show k + 1 ≤ d - 1 by omega)
        ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t
          (Shared.zmodVectorExtendZero
            (show k + 1 ≤ d - 1 by omega) y)) r -
        ((t : Nat) : ZMod m)
  have hG : Function.Bijective G := by
    simpa [G] using
      prefixCountFirstHitCanonicalSchedule_prefixMap_lowResidual_bijective
        (hd2 := hd2) (C := C) hdodd hd5 hmodd hdm hC L c t k hk
  let e : (Fin (k + 1) → ZMod m) ≃ (Fin (k + 1) → ZMod m) :=
    Equiv.ofBijective G hG
  calc
    (∑ y : Fin (k + 1) → ZMod m,
        F (fun r =>
          Shared.zmodVectorTake (show k + 1 ≤ d - 1 by omega)
            ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t
              (Shared.zmodVectorExtendZero
                (show k + 1 ≤ d - 1 by omega) y)) r -
            ((t : Nat) : ZMod m)))
        = ∑ y : Fin (k + 1) → ZMod m, F (e y) := by
            rfl
    _ = ∑ z : Fin (k + 1) → ZMod m, F z := by
            exact Fintype.sum_equiv e (fun y => F (e y)) F
              (by intro y; rfl)

theorem prefixCountFirstHitReturnLowResidualReindexGoal :
    PrefixCountFirstHitReturnLowResidualReindexGoal := by
  classical
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L c k hk t _ht F
  let hle : k + 1 ≤ d - 1 := by omega
  let baseStep := prefixCountFirstHitReturnBaseStep (m := m) C c
  let fiberStep := prefixCountFirstHitReturnFiberStep hd2 L c
  let P : (Fin (k + 1) → ZMod m) → (Fin (k + 1) → ZMod m) := fun y =>
    fun r =>
      Shared.zmodVectorTake hle
        ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t
          (Shared.zmodVectorExtendZero hle y)) r -
        ((t : Nat) : ZMod m)
  calc
    (∑ x : (Fin k → ZMod m),
        ∑ u ∈ Finset.range m,
          F (prefixCountFirstHitReturnLowResidual hd2 L c hk t u x))
        =
        ∑ u ∈ Finset.range m,
          ∑ x : (Fin k → ZMod m),
            F (P (Fin.cons ((baseStep^[u]) (0 : ZMod m))
              (Shared.zmodVectorTake (Nat.le_of_lt hk)
                (Shared.skewFiberIterate baseStep fiberStep u (0 : ZMod m)
                  (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x))))) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro u _hu
          apply Finset.sum_congr rfl
          intro x _hx
          change
            F (prefixCountFirstHitLowResidualFromHeadTail hd2 L c hk t
              ((baseStep^[u]) (0 : ZMod m))
              (Shared.skewFiberIterate baseStep fiberStep u (0 : ZMod m)
                (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x))) =
            F (P (Fin.cons ((baseStep^[u]) (0 : ZMod m))
              (Shared.zmodVectorTake (Nat.le_of_lt hk)
                (Shared.skewFiberIterate baseStep fiberStep u (0 : ZMod m)
                  (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x)))))
          rw [prefixCountFirstHitLowResidualFromHeadTail_eq_lowPrefix
            (hd2 := hd2) (C := C) L c hk t
            ((baseStep^[u]) (0 : ZMod m))
            (Shared.skewFiberIterate baseStep fiberStep u (0 : ZMod m)
              (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x))
            (Shared.zmodVectorTake (Nat.le_of_lt hk)
              (Shared.skewFiberIterate baseStep fiberStep u (0 : ZMod m)
                (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x)))
            rfl]
    _ =
        ∑ u ∈ Finset.range m,
          ∑ y : (Fin k → ZMod m),
            F (P (Fin.cons ((baseStep^[u]) (0 : ZMod m)) y)) := by
          apply Finset.sum_congr rfl
          intro u _hu
          let G : (Fin k → ZMod m) → (Fin k → ZMod m) := fun x =>
            Shared.zmodVectorTake (Nat.le_of_lt hk)
              (Shared.skewFiberIterate baseStep fiberStep u (0 : ZMod m)
                (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x))
          have hG : Function.Bijective G := by
            simpa [G, baseStep, fiberStep] using
              prefixCountFirstHitSkewFiberIterate_lowPrefix_bijective
                (hd2 := hd2) (C := C)
                hdodd hd5 hmodd hdm hC L c u k hk
          let e : (Fin k → ZMod m) ≃ (Fin k → ZMod m) :=
            Equiv.ofBijective G hG
          calc
            (∑ x : (Fin k → ZMod m),
              F (P (Fin.cons ((baseStep^[u]) (0 : ZMod m))
                (Shared.zmodVectorTake (Nat.le_of_lt hk)
                  (Shared.skewFiberIterate baseStep fiberStep u (0 : ZMod m)
                    (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x))))))
                =
                ∑ x : (Fin k → ZMod m),
                  F (P (Fin.cons ((baseStep^[u]) (0 : ZMod m)) (e x))) := by
                  rfl
            _ =
                ∑ y : (Fin k → ZMod m),
                  F (P (Fin.cons ((baseStep^[u]) (0 : ZMod m)) y)) := by
                  exact Fintype.sum_equiv e
                    (fun x => F (P (Fin.cons ((baseStep^[u]) (0 : ZMod m)) (e x))))
                    (fun y => F (P (Fin.cons ((baseStep^[u]) (0 : ZMod m)) y)))
                    (by intro x; rfl)
    _ =
        ∑ z : ZMod m,
          ∑ y : (Fin k → ZMod m),
            F (P (Fin.cons z y)) := by
          simpa [baseStep] using
            prefixCountFirstHitReturnBaseStep_sum_range_iterate
              (m := m) hC c
              (fun z : ZMod m =>
                ∑ y : (Fin k → ZMod m), F (P (Fin.cons z y)))
    _ =
        ∑ p : ZMod m × (Fin k → ZMod m),
          F (P (Fin.cons p.1 p.2)) := by
          rw [Fintype.sum_prod_type]
    _ =
        ∑ y : Fin (k + 1) → ZMod m, F (P y) := by
          let e : ZMod m × (Fin k → ZMod m) ≃
              (Fin (k + 1) → ZMod m) :=
            (Shared.zmodVectorConsEquiv k m).symm
          exact Fintype.sum_equiv e
            (fun p : ZMod m × (Fin k → ZMod m) =>
              F (P (Fin.cons p.1 p.2)))
            (fun y : Fin (k + 1) → ZMod m => F (P y))
            (by
              intro p
              rcases p with ⟨z, y⟩
              simp [e])
    _ = ∑ y : Fin (k + 1) → ZMod m, F y := by
          simpa [P, hle] using
            prefixCountFirstHitCanonicalSchedule_prefixMap_lowResidual_sum
              (hd2 := hd2) (C := C) hdodd hd5 hmodd hdm hC L c t k hk F

theorem prefixCountFirstHitReturnTailIncrementDependsOnTakeGoal_of_fiber
    (hFiber : PrefixCountFirstHitReturnFiberIncrementDependsOnTakeGoal) :
    PrefixCountFirstHitReturnTailIncrementDependsOnTakeGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L c tail k hk
  let low : Fin k → ZMod m :=
    Shared.zmodVectorTake (Nat.le_of_lt hk) tail
  let y : Fin (d - 2) → ZMod m :=
    Shared.zmodVectorExtendZero (Nat.le_of_lt hk) low
  have hmap :
      Shared.ZModVectorIncrementDependsOnTake
        (prefixCountFirstHitReturnTailMonodromy hd2 L c) := by
    rw [prefixCountFirstHitReturnTailMonodromy_eq_fiberIterate
      (hd2 := hd2) (C := C) L c]
    exact
      Shared.zmodVectorIncrementDependsOnTake_skewFiberIterate
        (prefixCountFirstHitReturnBaseStep (m := m) C c)
        (prefixCountFirstHitReturnFiberStep hd2 L c)
        (fun z => hFiber hd2 hdodd hd5 hmodd hdm hC L c z)
        m (0 : ZMod m)
  have htake :
      Shared.zmodVectorTake (Nat.le_of_lt hk) tail =
        Shared.zmodVectorTake (Nat.le_of_lt hk) y := by
    simp [y, low]
  have hdep := hmap tail y k hk htake
  have hyk : y ⟨k, hk⟩ = 0 := by
    simp [y]
  change
    prefixCountFirstHitReturnTailMonodromy hd2 L c tail ⟨k, hk⟩ -
        tail ⟨k, hk⟩ =
      prefixCountFirstHitReturnTailCocycle hd2 L c k hk low
  rw [hdep, hyk, sub_zero]
  rfl

theorem prefixCountFirstHitReturnTailTriangularGoal_of_incrementDependsOnTake
    (hInc : PrefixCountFirstHitReturnTailIncrementDependsOnTakeGoal) :
    PrefixCountFirstHitReturnTailTriangularGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L c tail k hk
  have h :=
    hInc hd2 hdodd hd5 hmodd hdm hC L c tail k hk
  calc
    prefixCountFirstHitReturnTailMonodromy hd2 L c tail ⟨k, hk⟩
        =
        tail ⟨k, hk⟩ +
          (prefixCountFirstHitReturnTailMonodromy hd2 L c tail ⟨k, hk⟩ -
            tail ⟨k, hk⟩) := by
          abel
    _ =
        tail ⟨k, hk⟩ +
          prefixCountFirstHitReturnTailCocycle hd2 L c k hk
            (Shared.zmodVectorTake (Nat.le_of_lt hk) tail) := by
          rw [h]

theorem prefixCountFirstHitReturnTailLocalHitConditionSum_eq_signedCoeff_of_reindex
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d)
    {k : Nat} (hk : k < d - 2) {t : Nat} (_ht : t ∈ Finset.range m)
    (R : Nat → (Fin k → ZMod m) → (Fin (k + 1) → ZMod m))
    (hReindex :
      ∀ F : (Fin (k + 1) → ZMod m) → ZMod m,
        (∑ x : (Fin k → ZMod m),
          ∑ u ∈ Finset.range m, F (R u x)) =
          ∑ y : (Fin (k + 1) → ZMod m), F y)
    (hHit :
      ∀ x : Fin k → ZMod m, ∀ u ∈ Finset.range m,
        prefixCountFirstHitReturnFiberHitCondition hd2 L c
            (((prefixCountFirstHitReturnBaseStep (m := m) C c)^[u])
              (0 : ZMod m))
            (Shared.skewFiberIterate
              (prefixCountFirstHitReturnBaseStep (m := m) C c)
              (prefixCountFirstHitReturnFiberStep hd2 L c)
              u (0 : ZMod m)
              (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x))
            ⟨k, hk⟩ t ↔
          (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c =
              prefixCountReturnTailDeltaCol hd2 ∧
                prefixCountPcExactLastZero (R u x)) ∨
            ((L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c).val =
                k + 1 ∧
              1 < (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c).val ∧
                prefixCountPcHitBeforeLastZero (R u x)) ∨
            (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c =
              prefixCountReturnTailStepCol hd2 hk ∧
                prefixCountPcNoZero (R u x))) :
    (∑ x : (Fin k → ZMod m),
      ∑ u ∈ Finset.range m,
        if prefixCountFirstHitReturnFiberHitCondition hd2 L c
            (((prefixCountFirstHitReturnBaseStep (m := m) C c)^[u])
              (0 : ZMod m))
            (Shared.skewFiberIterate
              (prefixCountFirstHitReturnBaseStep (m := m) C c)
              (prefixCountFirstHitReturnFiberStep hd2 L c)
              u (0 : ZMod m)
              (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x))
            ⟨k, hk⟩ t
        then (1 : ZMod m) else 0) =
      prefixCountReturnTailSignedCoeff hd2 hk
        (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c) := by
  classical
  let s := L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c
  let F : (Fin (k + 1) → ZMod m) → ZMod m := fun y =>
    if
      (s = prefixCountReturnTailDeltaCol hd2 ∧
          prefixCountPcExactLastZero y) ∨
        (s.val = k + 1 ∧ 1 < s.val ∧
          prefixCountPcHitBeforeLastZero y) ∨
        (s = prefixCountReturnTailStepCol hd2 hk ∧
          prefixCountPcNoZero y)
    then (1 : ZMod m) else 0
  calc
    (∑ x : (Fin k → ZMod m),
      ∑ u ∈ Finset.range m,
        if prefixCountFirstHitReturnFiberHitCondition hd2 L c
            (((prefixCountFirstHitReturnBaseStep (m := m) C c)^[u])
              (0 : ZMod m))
            (Shared.skewFiberIterate
              (prefixCountFirstHitReturnBaseStep (m := m) C c)
              (prefixCountFirstHitReturnFiberStep hd2 L c)
              u (0 : ZMod m)
              (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x))
            ⟨k, hk⟩ t
        then (1 : ZMod m) else 0)
        =
        ∑ x : (Fin k → ZMod m),
          ∑ u ∈ Finset.range m, F (R u x) := by
          apply Finset.sum_congr rfl
          intro x _hx
          apply Finset.sum_congr rfl
          intro u hu
          have hiff := hHit x u hu
          by_cases hP :
              prefixCountFirstHitReturnFiberHitCondition hd2 L c
                (((prefixCountFirstHitReturnBaseStep (m := m) C c)^[u])
                  (0 : ZMod m))
                (Shared.skewFiberIterate
                  (prefixCountFirstHitReturnBaseStep (m := m) C c)
                  (prefixCountFirstHitReturnFiberStep hd2 L c)
                  u (0 : ZMod m)
                  (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x))
                ⟨k, hk⟩ t
          · have hQ := hiff.mp hP
            simp [F, s, hP, hQ]
          · have hQ :
                ¬ ((L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c =
                    prefixCountReturnTailDeltaCol hd2 ∧
                      prefixCountPcExactLastZero (R u x)) ∨
                  ((L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c).val =
                      k + 1 ∧
                    1 < (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c).val ∧
                      prefixCountPcHitBeforeLastZero (R u x)) ∨
                  (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c =
                    prefixCountReturnTailStepCol hd2 hk ∧
                      prefixCountPcNoZero (R u x))) := by
              intro hQ
              exact hP (hiff.mpr hQ)
            simp [F, s, hP, hQ]
    _ = ∑ y : (Fin (k + 1) → ZMod m), F y := hReindex F
    _ =
        prefixCountReturnTailSignedCoeff hd2 hk
          (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c) := by
          simpa [F, s] using
            prefixCountReturnTailLocalSymbolSplitIndicatorSum
              (m := m) hd2 hk
              (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c)

theorem prefixCountFirstHitReturnTailLocalHitConditionSumGoal_of_lowResidualReindex
    (hReindex : PrefixCountFirstHitReturnLowResidualReindexGoal) :
    PrefixCountFirstHitReturnTailLocalHitConditionSumGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L c k hk t ht
  exact
    prefixCountFirstHitReturnTailLocalHitConditionSum_eq_signedCoeff_of_reindex
      (hd2 := hd2) (C := C) L c hk ht
      (fun u x => prefixCountFirstHitReturnLowResidual hd2 L c hk t u x)
      (by
        intro F
        exact hReindex hd2 hdodd hd5 hmodd hdm hC L c k hk t ht F)
      (by
        intro x u _hu
        exact
          prefixCountFirstHitReturnFiberHitCondition_lowResidual_iff
            (hd2 := hd2) (C := C) L c hk t u x)

theorem prefixCountFirstHitReturnTailCocycleSumGoal_of_localHitConditionSum
    (hLocal : PrefixCountFirstHitReturnTailLocalHitConditionSumGoal) :
    PrefixCountFirstHitReturnTailCocycleSumGoal := by
  classical
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L c k hk
  let f : (Fin k → ZMod m) → Nat → Nat → ZMod m := fun x u t =>
    if prefixCountFirstHitReturnFiberHitCondition hd2 L c
        (((prefixCountFirstHitReturnBaseStep (m := m) C c)^[u])
          (0 : ZMod m))
        (Shared.skewFiberIterate
          (prefixCountFirstHitReturnBaseStep (m := m) C c)
          (prefixCountFirstHitReturnFiberStep hd2 L c)
          u (0 : ZMod m)
          (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x))
        ⟨k, hk⟩ t
    then (1 : ZMod m) else 0
  calc
    (∑ x : (Fin k → ZMod m),
        prefixCountFirstHitReturnTailCocycle hd2 L c k hk x)
        =
        ∑ x : (Fin k → ZMod m),
          ∑ u ∈ Finset.range m,
            ∑ t ∈ Finset.range m, f x u t := by
          apply Finset.sum_congr rfl
          intro x _hx
          rw [prefixCountFirstHitReturnTailCocycle_eq_sum_hitCondition
            (hd2 := hd2) (C := C) L c k hk x]
    _ =
        ∑ u ∈ Finset.range m,
          ∑ x : (Fin k → ZMod m),
            ∑ t ∈ Finset.range m, f x u t := by
          rw [Finset.sum_comm]
    _ =
        ∑ u ∈ Finset.range m,
          ∑ t ∈ Finset.range m,
            ∑ x : (Fin k → ZMod m), f x u t := by
          apply Finset.sum_congr rfl
          intro u _hu
          rw [Finset.sum_comm]
    _ =
        ∑ t ∈ Finset.range m,
          ∑ u ∈ Finset.range m,
            ∑ x : (Fin k → ZMod m), f x u t := by
          rw [Finset.sum_comm]
    _ =
        ∑ t ∈ Finset.range m,
          ∑ x : (Fin k → ZMod m),
            ∑ u ∈ Finset.range m, f x u t := by
          apply Finset.sum_congr rfl
          intro t _ht
          rw [Finset.sum_comm]
    _ =
        ∑ t ∈ Finset.range m,
          prefixCountReturnTailSignedCoeff hd2 hk
            (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c) := by
          apply Finset.sum_congr rfl
          intro t ht
          simpa [f] using
            hLocal hd2 hdodd hd5 hmodd hdm hC L c k hk t ht
    _ =
        ((-1 : ZMod m) ^ (k + 1)) *
          ((((C.toMatrix hd2)
              c (prefixCountReturnTailStepCol hd2 hk) : Nat) : ZMod m) -
            (((C.toMatrix hd2)
              c (prefixCountReturnTailDeltaCol hd2) : Nat) : ZMod m)) := by
          exact prefixCountReturnTailSignedCoeff_layer_sum_eq_matrix
            (hd2 := hd2) (C := C) L c hk
    _ =
        ((-1 : ZMod m) ^ (k + 1)) *
          (((C.step c ⟨k, hk⟩ : Int) - (C.delta c : Int)) : ZMod m) := by
          have hmat :=
            prefixCount_toMatrix_rawStep_sub_delta_zmod
              (m := m) hd2 C c (k := k) hk
          simpa [prefixCountReturnTailStepCol, prefixCountReturnTailDeltaCol]
            using congrArg
              (fun q : ZMod m => ((-1 : ZMod m) ^ (k + 1)) * q) hmat

theorem prefixCountFirstHitReturnTailCocycleUnitGoal_of_sum
    (hSum : PrefixCountFirstHitReturnTailCocycleSumGoal) :
    PrefixCountFirstHitReturnTailCocycleUnitGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L c k hk
  rw [hSum hd2 hdodd hd5 hmodd hdm hC L c k hk]
  exact
    IsUnit.mul
      (IsUnit.pow (k + 1) (IsUnit.neg isUnit_one))
      (by
        simpa [Int.cast_sub, Int.cast_natCast] using
          PrefixCount.isUnit_zmod_intCast_of_intCoprime
            (hC.prim_step c ⟨k, hk⟩))

theorem prefixCountFirstHitReturnTailLocalHitConditionSumGoal :
    PrefixCountFirstHitReturnTailLocalHitConditionSumGoal :=
  prefixCountFirstHitReturnTailLocalHitConditionSumGoal_of_lowResidualReindex
    prefixCountFirstHitReturnLowResidualReindexGoal

theorem prefixCountFirstHitReturnTailCocycleSumGoal :
    PrefixCountFirstHitReturnTailCocycleSumGoal :=
  prefixCountFirstHitReturnTailCocycleSumGoal_of_localHitConditionSum
    prefixCountFirstHitReturnTailLocalHitConditionSumGoal

theorem prefixCountFirstHitReturnTailCocycleUnitGoal :
    PrefixCountFirstHitReturnTailCocycleUnitGoal :=
  prefixCountFirstHitReturnTailCocycleUnitGoal_of_sum
    prefixCountFirstHitReturnTailCocycleSumGoal

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

theorem prefixCountFirstHitReturnTailCycleCoordinateGoal_of_triangular_unit
    (hLower : Shared.ZModVectorLowerTriangularUnitCycleCoordinateGoal)
    (hTri : PrefixCountFirstHitReturnTailTriangularGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal) :
    PrefixCountFirstHitReturnTailCycleCoordinateGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L c
  rcases hLower
    (m := m) (r := d - 2)
    (F := prefixCountFirstHitReturnTailMonodromy hd2 L c)
    (gamma := fun k hk =>
      prefixCountFirstHitReturnTailCocycle hd2 L c k hk)
    (by
      intro tail k hk
      exact hTri hd2 hdodd hd5 hmodd hdm hC L c tail k hk)
    (by
      intro k hk
      exact hUnit hd2 hdodd hd5 hmodd hdm hC L c k hk)
    with ⟨e, hstep⟩
  exact ⟨Shared.CycleCoordinate.ofRankEquiv e hstep⟩

theorem prefixCountFirstHitReturnTailCycleCoordinateGoal_of_triangularUnitBlocks
    (hBlocks : PrefixCountFirstHitReturnTailTriangularUnitBlocksGoal) :
    PrefixCountFirstHitReturnTailCycleCoordinateGoal :=
  prefixCountFirstHitReturnTailCycleCoordinateGoal_of_triangular_unit
    hBlocks.1 hBlocks.2.1 hBlocks.2.2

theorem prefixCountFirstHitReturnTailCycleCoordinateGoal_of_triangular_unit_closed
    (hTri : PrefixCountFirstHitReturnTailTriangularGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal) :
    PrefixCountFirstHitReturnTailCycleCoordinateGoal :=
  prefixCountFirstHitReturnTailCycleCoordinateGoal_of_triangular_unit
    Shared.zmodVectorLowerTriangularUnitCycleCoordinate hTri hUnit

theorem prefixCountFirstHitReturnTailCycleCoordinateGoal_of_triangularCocycleBlocks
    (hBlocks : PrefixCountFirstHitReturnTailTriangularCocycleBlocksGoal) :
    PrefixCountFirstHitReturnTailCycleCoordinateGoal :=
  prefixCountFirstHitReturnTailCycleCoordinateGoal_of_triangular_unit_closed
    hBlocks.1 hBlocks.2

theorem prefixCountFirstHitReturnTailCycleCoordinateGoal_of_incrementUnitBlocks
    (hBlocks : PrefixCountFirstHitReturnTailIncrementUnitBlocksGoal) :
    PrefixCountFirstHitReturnTailCycleCoordinateGoal :=
  prefixCountFirstHitReturnTailCycleCoordinateGoal_of_triangular_unit_closed
    (prefixCountFirstHitReturnTailTriangularGoal_of_incrementDependsOnTake
      hBlocks.1)
    hBlocks.2

theorem prefixCountFirstHitReturnTailCycleCoordinateGoal_of_fiberIncrementUnitBlocks
    (hBlocks : PrefixCountFirstHitReturnFiberIncrementUnitBlocksGoal) :
    PrefixCountFirstHitReturnTailCycleCoordinateGoal :=
  prefixCountFirstHitReturnTailCycleCoordinateGoal_of_incrementUnitBlocks
    ⟨prefixCountFirstHitReturnTailIncrementDependsOnTakeGoal_of_fiber
      hBlocks.1,
    hBlocks.2⟩

theorem prefixCountFirstHitReturnTailCycleCoordinateGoal_of_hitConditionUnitBlocks
    (hBlocks : PrefixCountFirstHitReturnFiberHitConditionUnitBlocksGoal) :
    PrefixCountFirstHitReturnTailCycleCoordinateGoal :=
  prefixCountFirstHitReturnTailCycleCoordinateGoal_of_fiberIncrementUnitBlocks
    ⟨prefixCountFirstHitReturnFiberIncrementDependsOnTakeGoal_of_hitCondition
      hBlocks.1,
    hBlocks.2⟩

theorem prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_triangular_unit
    (hLower : Shared.ZModVectorLowerTriangularUnitCycleCoordinateGoal)
    (hTri : PrefixCountFirstHitReturnTailTriangularGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal) :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal :=
  prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_cycleCoordinate
    (prefixCountFirstHitReturnTailCycleCoordinateGoal_of_triangular_unit
      hLower hTri hUnit)

theorem prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_triangularUnitBlocks
    (hBlocks : PrefixCountFirstHitReturnTailTriangularUnitBlocksGoal) :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal :=
  prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_triangular_unit
    hBlocks.1 hBlocks.2.1 hBlocks.2.2

theorem prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_triangular_unit_closed
    (hTri : PrefixCountFirstHitReturnTailTriangularGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal) :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal :=
  prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_cycleCoordinate
    (prefixCountFirstHitReturnTailCycleCoordinateGoal_of_triangular_unit_closed
      hTri hUnit)

theorem prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_triangularCocycleBlocks
    (hBlocks : PrefixCountFirstHitReturnTailTriangularCocycleBlocksGoal) :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal :=
  prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_triangular_unit_closed
    hBlocks.1 hBlocks.2

theorem prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_incrementUnitBlocks
    (hBlocks : PrefixCountFirstHitReturnTailIncrementUnitBlocksGoal) :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal :=
  prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_cycleCoordinate
    (prefixCountFirstHitReturnTailCycleCoordinateGoal_of_incrementUnitBlocks
      hBlocks)

theorem prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_fiberIncrementUnitBlocks
    (hBlocks : PrefixCountFirstHitReturnFiberIncrementUnitBlocksGoal) :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal :=
  prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_cycleCoordinate
    (prefixCountFirstHitReturnTailCycleCoordinateGoal_of_fiberIncrementUnitBlocks
      hBlocks)

theorem prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_hitConditionUnitBlocks
    (hBlocks : PrefixCountFirstHitReturnFiberHitConditionUnitBlocksGoal) :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal :=
  prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_cycleCoordinate
    (prefixCountFirstHitReturnTailCycleCoordinateGoal_of_hitConditionUnitBlocks
      hBlocks)

theorem prefixCountFirstHitReturnFiberHitConditionUnitBlocksGoal :
    PrefixCountFirstHitReturnFiberHitConditionUnitBlocksGoal :=
  ⟨prefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal,
    prefixCountFirstHitReturnTailCocycleUnitGoal⟩

theorem prefixCountFirstHitReturnTailCycleCoordinateGoal :
    PrefixCountFirstHitReturnTailCycleCoordinateGoal :=
  prefixCountFirstHitReturnTailCycleCoordinateGoal_of_hitConditionUnitBlocks
    prefixCountFirstHitReturnFiberHitConditionUnitBlocksGoal

theorem prefixCountFirstHitReturnTailMonodromyOrbitGoal :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal :=
  prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_hitConditionUnitBlocks
    prefixCountFirstHitReturnFiberHitConditionUnitBlocksGoal

theorem prefixCountFirstHitReturnTailMonodromyGoal_of_rank
    (hRank : PrefixCountFirstHitReturnTailRankGoal) :
    PrefixCountFirstHitReturnTailMonodromyGoal :=
  prefixCountFirstHitReturnTailMonodromyGoal_of_orbit
    (prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_rank hRank)

theorem prefixCountFirstHitReturnTailMonodromyGoal :
    PrefixCountFirstHitReturnTailMonodromyGoal :=
  prefixCountFirstHitReturnTailMonodromyGoal_of_orbit
    prefixCountFirstHitReturnTailMonodromyOrbitGoal

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

theorem prefixCountFirstHitReturnTailCycleCoordinateGoal_of_monodromy
    (hTail : PrefixCountFirstHitReturnTailMonodromyGoal) :
    PrefixCountFirstHitReturnTailCycleCoordinateGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L c
  have hcard :
      Fintype.card (Fin (d - 2) → ZMod m) = m ^ (d - 2) := by
    exact Shared.card_zmodVector (d - 2) m
  have hm1 : 1 < m := by omega
  have hexp : d - 2 ≠ 0 := by omega
  have hn : 1 < m ^ (d - 2) := one_lt_pow₀ hm1 hexp
  exact ⟨
    Shared.CycleCoordinate.ofFiniteSingleCycle
      (f := prefixCountFirstHitReturnTailMonodromy hd2 L c)
      hcard hn
      (hTail hd2 hdodd hd5 hmodd hdm hC L c)⟩

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

def OddSuccessorSmallModulusBaseTailGeometryFromHallGoal : Prop :=
  ActiveHall.HallRealizationGoal.{0, 0} →
    OddSuccessorSmallModulusSlackPacketLiftAddGoal

/--
The successor-small geometry target after the pure packet arithmetic has been
separated out.  Compared with
`OddSuccessorSmallModulusSlackPacketLiftAddGoal`, this core statement receives
the nonempty proper packet-prefix unit condition explicitly.
-/
def OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal : Prop :=
  ActiveHall.HallRealizationGoal.{0, 0} →
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
    (∀ packet, packet ∈ packets →
      ∀ q : Nat, 0 < q → q < packet.length →
        Nat.Coprime (packet.take q).sum m) →
    T = b + 1 →
    m ^ b > m * (b + T) * T →
    StandardCayleySolved (b + T) m

def OddSuccessorBaseTailCylinderConstructionGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m],
    5 ≤ b →
    Odd m → 3 ≤ m → m < b + T →
    StandardCayleySolved b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    (∀ packet, packet ∈ packets →
      ∀ q : Nat, 0 < q → q < packet.length →
        Nat.Coprime (packet.take q).sum m) →
    T = b + 1 →
    ∃ Cyl : BaseTail.Cylinder b m T packets,
      BaseTail.IsCylinder Cyl

def OddSuccessorBaseTailResidueRoundingGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m],
    5 ≤ b →
    Odd m → 3 ≤ m → m < b + T →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    (∀ packet, packet ∈ packets →
      ∀ q : Nat, 0 < q → q < packet.length →
        Nat.Coprime (packet.take q).sum m) →
    T = b + 1 →
    m ^ b > m * (b + T) * T →
    ∀ {Cyl : BaseTail.Cylinder b m T packets},
      BaseTail.IsCylinder Cyl →
      (hT2 : 2 ≤ T) →
        BaseTail.HasFeasiblePrimitiveResidues hT2 Cyl

def OddSuccessorBaseTailPrimitiveActiveLiftGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m],
    5 ≤ b →
    Odd m → 3 ≤ m → m < b + T →
    StandardCayleySolved b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    (∀ packet, packet ∈ packets →
      ∀ q : Nat, 0 < q → q < packet.length →
        Nat.Coprime (packet.take q).sum m) →
    T = b + 1 →
    m ^ b > m * (b + T) * T →
    ∀ {Cyl : BaseTail.Cylinder b m T packets}
      {A : BaseTail.ActiveSymboling Cyl},
      BaseTail.IsCylinder Cyl →
      (hT2 : 2 ≤ T) →
      BaseTail.IsPrimitiveActiveSymboling hT2 A →
      StandardCayleySolved (b + T) m

theorem oddSuccessorBaseTailPrimitiveActiveLiftGoal_of_primitiveActiveLiftAssembly
    (hLift : BaseTail.PrimitiveActiveLiftAssemblyGoal) :
    OddSuccessorBaseTailPrimitiveActiveLiftGoal := by
  intro b m T _inst _hb5 _hmodd _hm3 _hsmall _hbase packets
    _hlen _htotal _hpacketSum _hpacketUnits _hPrefix _hT _hSlack
    Cyl A hCyl hT2 hA
  exact hLift hT2 hCyl hA

theorem oddSuccessorBaseTailPrimitiveActiveLiftGoal_of_prefixLiftAssembly
    (hLift : BaseTail.PrimitiveActivePrefixLiftAssemblyGoal) :
    OddSuccessorBaseTailPrimitiveActiveLiftGoal :=
  oddSuccessorBaseTailPrimitiveActiveLiftGoal_of_primitiveActiveLiftAssembly
    (BaseTail.primitiveActiveLiftAssemblyGoal_of_prefixLiftAssembly hLift)

theorem oddSuccessorBaseTailPrimitiveActiveLiftGoal_of_expandedColorDirHamiltonian
    (hHam : BaseTail.ExpandedColorDirColorHamiltonianGoal) :
    OddSuccessorBaseTailPrimitiveActiveLiftGoal :=
  oddSuccessorBaseTailPrimitiveActiveLiftGoal_of_primitiveActiveLiftAssembly
    (BaseTail.primitiveActiveLiftAssemblyGoal_of_expandedColorDirHamiltonian
      hHam)

def OddSuccessorBaseTailActiveBlockCylinderConstructionGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m],
    5 ≤ b →
    Odd m → 3 ≤ m → m < b + T →
    StandardCayleySolved b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    (∀ packet, packet ∈ packets →
      ∀ q : Nat, 0 < q → q < packet.length →
        Nat.Coprime (packet.take q).sum m) →
    T = b + 1 →
    ∃ Cyl : BaseTail.Cylinder b m T packets,
      ∃ _D : BaseTail.ActiveBlockData Cyl,
        BaseTail.IsCylinder Cyl

/--
Raw construction target for the active-block cylinder.

The active block degree formula already implies the `active_degree_mod` field
of `BaseTail.IsCylinder`; the genuine geometric work is to construct the
cylinder, prove ordinary directions are unique, prove each compressed color
step is Hamiltonian, and compute the active block degrees.
-/
def OddSuccessorBaseTailRawActiveBlockCylinderConstructionGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m],
    5 ≤ b →
    Odd m → 3 ≤ m → m < b + T →
    StandardCayleySolved b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    (∀ packet, packet ∈ packets →
      ∀ q : Nat, 0 < q → q < packet.length →
        Nat.Coprime (packet.take q).sum m) →
    T = b + 1 →
    ∃ Cyl : BaseTail.Cylinder b m T packets,
      ∃ _D : BaseTail.ActiveBlockData Cyl,
        (∀ x : Shared.TorusVertex (b + 1) m,
          ∀ i : Fin (b + 1), i ≠ BaseTail.activeDir b →
            ∃! c : Fin (b + T), Cyl.dir c x = i) ∧
        (∀ c : Fin (b + T), Shared.IsSingleCycleMap (Cyl.step c))

/--
Phase-split construction target for the active-block cylinder.

The base Hamilton decomposition supplies the compressed base color cycles.
The separate `PacketPhaseSplitGoal` supplies the one-packet splitter on each
base cycle.  This goal is the remaining assembly theorem turning those local
splitters into the raw active-block cylinder data.
-/
def OddSuccessorBaseTailPhaseSplitActiveBlockCylinderConstructionGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] [NeZero (m ^ b)],
    5 ≤ b →
    3 ≤ m →
    Shared.CayleyDecomposition b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    (∀ packet, packet ∈ packets →
      ∀ q : Nat, 0 < q → q < packet.length →
        Nat.Coprime (packet.take q).sum m) →
    (∀ packet, packet ∈ packets →
      Nonempty (BaseTail.PacketPhaseSplit (m ^ b) m packet)) →
    T = b + 1 →
    ∃ Cyl : BaseTail.Cylinder b m T packets,
      ∃ _D : BaseTail.ActiveBlockData Cyl,
        (∀ x : Shared.TorusVertex (b + 1) m,
          ∀ i : Fin (b + 1), i ≠ BaseTail.activeDir b →
            ∃! c : Fin (b + T), Cyl.dir c x = i) ∧
        (∀ c : Fin (b + T), Shared.IsSingleCycleMap (Cyl.step c))

def OddSuccessorBaseTailCoordinatizedPhaseSplitActiveBlockCylinderConstructionGoal :
    Prop :=
  ∀ {b m T : Nat} [NeZero m] [NeZero (m ^ b)],
    5 ≤ b →
    3 ≤ m →
    Shared.CoordinatizedCayleyDecomposition b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    (∀ packet, packet ∈ packets →
      ∀ q : Nat, 0 < q → q < packet.length →
        Nat.Coprime (packet.take q).sum m) →
    (∀ packet, packet ∈ packets →
      Nonempty (BaseTail.PacketPhaseSplit (m ^ b) m packet)) →
    T = b + 1 →
    ∃ Cyl : BaseTail.Cylinder b m T packets,
      ∃ _D : BaseTail.ActiveBlockData Cyl,
        (∀ x : Shared.TorusVertex (b + 1) m,
          ∀ i : Fin (b + 1), i ≠ BaseTail.activeDir b →
            ∃! c : Fin (b + T), Cyl.dir c x = i) ∧
        (∀ c : Fin (b + T), Shared.IsSingleCycleMap (Cyl.step c))

theorem oddSuccessorBaseTailCoordinatizedPhaseSplitActiveBlockCylinderConstructionGoal :
    OddSuccessorBaseTailCoordinatizedPhaseSplitActiveBlockCylinderConstructionGoal := by
  classical
  intro b m T _instM _instPow _hb5 hm3 Dbase packets hlen htotal
    hpacketSum hpacketUnits _hPrefix hPacketSplits _hT
  let slotEquiv : BaseTail.PacketPartSlot packets ≃ Fin (b + T) :=
    Classical.choice (BaseTail.successorPacketPartSlotEquivGoal hlen htotal)
  let S : ∀ i : Fin packets.length,
      BaseTail.PacketPhaseSplit (m ^ b) m (packets.get i) :=
    fun i =>
      Classical.choice
        (hPacketSplits (packets.get i) (List.get_mem packets i))
  let baseColorOfSlot : BaseTail.PacketPartSlot packets → Fin b :=
    fun slot => Fin.cast hlen slot.1
  let rankAt : Shared.TorusVertex (b + 1) m → Fin packets.length →
      ZMod (m ^ b) :=
    fun x i =>
      (Dbase.cycleCoordinate (Fin.cast hlen i)).equiv.symm
        (BaseTail.basePart x)
  let ordinaryAt : Fin (b + T) → Shared.TorusVertex (b + 1) m → Bool :=
    fun c x =>
      (S (slotEquiv.symm c).1).ordinary (slotEquiv.symm c).2
        (rankAt x (slotEquiv.symm c).1, BaseTail.activeCoord x)
  let dir : Fin (b + T) → Shared.TorusVertex (b + 1) m → Fin (b + 1) :=
    fun c x =>
      if ordinaryAt c x then
        (Dbase.colorDir (baseColorOfSlot (slotEquiv.symm c))
          (BaseTail.basePart x)).castSucc
      else
        BaseTail.activeDir b
  let Cyl : BaseTail.Cylinder b m T packets :=
    {
      dir := dir
      active_card := by
        intro x
        simpa [dir, ordinaryAt, rankAt, BaseTail.castSucc_ne_activeDir] using
          BaseTail.packetPartColor_false_card_at_state_successor
            packets slotEquiv hm3 hlen htotal hpacketSum hpacketUnits
            S (fun i => rankAt x i) (BaseTail.activeCoord x)
    }
  let D : BaseTail.ActiveBlockData Cyl :=
    {
      activeBlock := fun c =>
        BaseTail.packetPartSlotValue packets (slotEquiv.symm c)
      activeBlock_pos := by
        intro c
        exact
          (BaseTail.successorPacketPartSlotUnitsGoal
            hlen htotal hpacketUnits (slotEquiv.symm c)).1
      activeBlock_lt := by
        intro c
        exact
          (BaseTail.successorPacketPartSlotUnitsGoal
            hlen htotal hpacketUnits (slotEquiv.symm c)).2.1
      activeBlock_coprime := by
        intro c
        exact
          (BaseTail.successorPacketPartSlotUnitsGoal
            hlen htotal hpacketUnits (slotEquiv.symm c)).2.2
      active_degree_eq := by
        intro c
        let slot := slotEquiv.symm c
        let baseColor : Fin b := baseColorOfSlot slot
        let C := Dbase.cycleCoordinate baseColor
        have hslotUnits :=
          BaseTail.successorPacketPartSlotUnitsGoal
            hlen htotal hpacketUnits slot
        have hfalse :=
          (S slot.1).ordinary_false_card_of_equiv
            (BaseTail.baseActiveRankEquiv C) slot.2
            (Nat.le_of_lt hslotUnits.2.1)
        simpa [ActiveHall.Incidence.colorDegree, BaseTail.Cylinder.incidence,
          BaseTail.Cylinder.active, Cyl, dir, ordinaryAt, rankAt,
          baseColorOfSlot, slot, baseColor, C,
          BaseTail.baseActiveRankEquiv_apply, BaseTail.castSucc_ne_activeDir]
          using hfalse
    }
  refine ⟨Cyl, D, ?_, ?_⟩
  · intro x i hi
    have hiv : i.val < b := by
      by_contra hnot
      have hlast : i = BaseTail.activeDir b := by
        apply Fin.ext
        simp [BaseTail.activeDir]
        omega
      exact hi hlast
    let j : Fin b := ⟨i.val, hiv⟩
    have hj_cast : j.castSucc = i := by
      apply Fin.ext
      rfl
    rcases Dbase.edgePartition (BaseTail.basePart x) j with
      ⟨baseColor, hbaseColor, hbaseUnique⟩
    let packetIndex : Fin packets.length := Fin.cast hlen.symm baseColor
    let y : ZMod (m ^ b) × ZMod m :=
      (rankAt x packetIndex, BaseTail.activeCoord x)
    rcases (S packetIndex).ordinary_unique y with
      ⟨part, hpart, hpartUnique⟩
    let slot : BaseTail.PacketPartSlot packets := ⟨packetIndex, part⟩
    refine ⟨slotEquiv slot, ?_, ?_⟩
    · have hbaseCast : baseColorOfSlot slot = baseColor := by
        simp [baseColorOfSlot, slot, packetIndex]
      have hordCand : ordinaryAt (slotEquiv slot) x = true := by
        change
          (S (slotEquiv.symm (slotEquiv slot)).1).ordinary
              (slotEquiv.symm (slotEquiv slot)).2
              (rankAt x (slotEquiv.symm (slotEquiv slot)).1,
                BaseTail.activeCoord x) = true
        rw [Equiv.symm_apply_apply]
        simpa [slot, y] using hpart
      simp [Cyl, dir, hordCand, hbaseCast,
        hbaseColor, hj_cast]
    · intro c hc
      have hordinary' :
          (S (slotEquiv.symm c).1).ordinary (slotEquiv.symm c).2
            (rankAt x (slotEquiv.symm c).1, BaseTail.activeCoord x) =
              true := by
        by_cases hord :
            (S (slotEquiv.symm c).1).ordinary (slotEquiv.symm c).2
              (rankAt x (slotEquiv.symm c).1, BaseTail.activeCoord x)
        · simpa using hord
        · exfalso
          have hdirActive : Cyl.dir c x = BaseTail.activeDir b := by
            simpa [Cyl, dir, ordinaryAt, hord]
          exact hi (hc.symm.trans hdirActive)
      have hdirCast :
          (Dbase.colorDir (baseColorOfSlot (slotEquiv.symm c))
            (BaseTail.basePart x)).castSucc =
            i := by
        simpa [Cyl, dir, ordinaryAt, hordinary'] using hc
      have hbaseEqJ :
          Dbase.colorDir (baseColorOfSlot (slotEquiv.symm c))
            (BaseTail.basePart x) = j := by
        apply Fin.ext
        have hv := congrArg Fin.val hdirCast
        simpa [hj_cast] using hv
      have hbaseEq : baseColorOfSlot (slotEquiv.symm c) = baseColor :=
        hbaseUnique (baseColorOfSlot (slotEquiv.symm c)) hbaseEqJ
      have hpacketEq : (slotEquiv.symm c).1 = packetIndex := by
        apply Fin.ext
        have hv := congrArg Fin.val hbaseEq
        simp [baseColorOfSlot, packetIndex] at hv ⊢
        exact hv
      have hslotEq : slotEquiv.symm c = slot := by
        cases hraw : slotEquiv.symm c with
        | mk packetIndex' part' =>
          rw [hraw] at hpacketEq hordinary'
          dsimp [slot] at hpacketEq hordinary' ⊢
          subst packetIndex'
          have hpartEq : part' = part := by
            exact hpartUnique part' (by simpa [y] using hordinary')
          subst part'
          rfl
      calc
        c = slotEquiv (slotEquiv.symm c) := by simp
        _ = slotEquiv slot := by rw [hslotEq]
  · intro c
    let slot : BaseTail.PacketPartSlot packets := slotEquiv.symm c
    let baseColor : Fin b := baseColorOfSlot slot
    let C := Dbase.cycleCoordinate baseColor
    let g : ZMod (m ^ b) × ZMod m → ZMod (m ^ b) × ZMod m :=
      fun y =>
        if (S slot.1).ordinary slot.2 y then
          (y.1 + 1, y.2)
        else
          (y.1, y.2 + 1)
    refine
      Shared.single_cycle_of_equiv_conj
        (BaseTail.baseActiveRankEquiv C).symm
        (Cyl.step c) g
        ((S slot.1).step_singleCycle slot.2) ?_
    intro y
    rcases y with ⟨z, a⟩
    by_cases hord : (S slot.1).ordinary slot.2 (z, a)
    · have hstep :
          Shared.cayleyColorStep Dbase.colorDir baseColor (C.equiv z) =
            C.equiv z +
              Shared.torusBasis b m
                (Dbase.colorDir baseColor (C.equiv z)) := rfl
      simpa [Cyl, BaseTail.Cylinder.step, dir, ordinaryAt, rankAt,
        baseColorOfSlot, slot, baseColor, C, g, hord,
        Shared.cayleyColorStep] using
        BaseTail.baseActiveRankEquiv_add_castSucc_of_step
          C (C.equiv z) a
          (Dbase.colorDir baseColor (C.equiv z)) hstep
    · simpa [Cyl, BaseTail.Cylinder.step, dir, ordinaryAt, rankAt,
        baseColorOfSlot, slot, baseColor, C, g, hord] using
        BaseTail.baseActiveRankEquiv_add_activeDir C (C.equiv z) a

/--
Phase-split construction target for the full mixed active-block cylinder.

This is weaker and more geometric than asking for mixed witnesses for every
possible active-block cylinder: the phase-split construction may return the
cylinder, the active-block degree data, and the mixed expansion data together.
-/
def OddSuccessorBaseTailPhaseSplitActiveBlockMixedCylinderConstructionGoal :
    Prop :=
  ∀ {b m T : Nat} [NeZero m] [NeZero (m ^ b)],
    5 ≤ b →
    3 ≤ m →
    Shared.CayleyDecomposition b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    (∀ packet, packet ∈ packets →
      ∀ q : Nat, 0 < q → q < packet.length →
        Nat.Coprime (packet.take q).sum m) →
    (∀ packet, packet ∈ packets →
      Nonempty (BaseTail.PacketPhaseSplit (m ^ b) m packet)) →
    T = b + 1 →
    ∃ Cyl : BaseTail.Cylinder b m T packets,
      ∃ _D : BaseTail.ActiveBlockData Cyl,
      ∃ _Mix : BaseTail.MixedExpansionData Cyl,
        BaseTail.IsCylinder Cyl

theorem oddSuccessorBaseTailPhaseSplitActiveBlockCylinderConstructionGoal_of_coordinatized
    (hBuild :
      OddSuccessorBaseTailCoordinatizedPhaseSplitActiveBlockCylinderConstructionGoal) :
    OddSuccessorBaseTailPhaseSplitActiveBlockCylinderConstructionGoal := by
  intro b m T _instM _instPow hb5 hm3 Dbase packets hlen htotal
    hpacketSum hpacketUnits hPrefix hPacketSplits hT
  have hpow : 1 < m ^ b := by
    exact Nat.one_lt_pow (by omega : b ≠ 0) (by omega : 1 < m)
  exact
    hBuild hb5 hm3
      (Shared.coordinatizedCayleyDecomposition_of_single_cycle hpow Dbase)
      packets hlen htotal hpacketSum hpacketUnits hPrefix hPacketSplits hT

theorem oddSuccessorBaseTailPhaseSplitActiveBlockCylinderConstructionGoal :
    OddSuccessorBaseTailPhaseSplitActiveBlockCylinderConstructionGoal :=
  oddSuccessorBaseTailPhaseSplitActiveBlockCylinderConstructionGoal_of_coordinatized
    oddSuccessorBaseTailCoordinatizedPhaseSplitActiveBlockCylinderConstructionGoal

def OddSuccessorBaseTailCoordinatizedPhaseSplitActiveBlockMixedCylinderConstructionGoal :
    Prop :=
  ∀ {b m T : Nat} [NeZero m] [NeZero (m ^ b)],
    5 ≤ b →
    3 ≤ m →
    Shared.CoordinatizedCayleyDecomposition b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    (∀ packet, packet ∈ packets →
      ∀ q : Nat, 0 < q → q < packet.length →
        Nat.Coprime (packet.take q).sum m) →
    (∀ packet, packet ∈ packets →
      Nonempty (BaseTail.PacketPhaseSplit (m ^ b) m packet)) →
    T = b + 1 →
    ∃ Cyl : BaseTail.Cylinder b m T packets,
      ∃ _D : BaseTail.ActiveBlockData Cyl,
      ∃ _Mix : BaseTail.MixedExpansionData Cyl,
        BaseTail.IsCylinder Cyl

theorem oddSuccessorBaseTailPhaseSplitActiveBlockMixedCylinderConstructionGoal_of_coordinatized
    (hBuild :
      OddSuccessorBaseTailCoordinatizedPhaseSplitActiveBlockMixedCylinderConstructionGoal) :
    OddSuccessorBaseTailPhaseSplitActiveBlockMixedCylinderConstructionGoal := by
  intro b m T _instM _instPow hb5 hm3 Dbase packets hlen htotal
    hpacketSum hpacketUnits hPrefix hPacketSplits hT
  have hpow : 1 < m ^ b := by
    exact Nat.one_lt_pow (by omega : b ≠ 0) (by omega : 1 < m)
  exact
    hBuild hb5 hm3
      (Shared.coordinatizedCayleyDecomposition_of_single_cycle hpow Dbase)
      packets hlen htotal hpacketSum hpacketUnits hPrefix hPacketSplits hT

theorem oddSuccessorBaseTailPhaseSplitActiveBlockMixedCylinderConstructionGoal_of_activeBlock
    (hBuild : OddSuccessorBaseTailPhaseSplitActiveBlockCylinderConstructionGoal) :
    OddSuccessorBaseTailPhaseSplitActiveBlockMixedCylinderConstructionGoal := by
  intro b m T _instM _instPow hb5 hm3 Dbase packets hlen htotal
    hpacketSum hpacketUnits hPrefix hPacketSplits hT
  rcases hBuild hb5 hm3 Dbase packets hlen htotal hpacketSum
      hpacketUnits hPrefix hPacketSplits hT with
    ⟨Cyl, D, hOrdinary, hHamiltonian⟩
  refine ⟨Cyl, D, D.mixedExpansionData_of_successor hT, ?_⟩
  exact D.isCylinder_of_activeBlockData hOrdinary hHamiltonian (by omega)

theorem oddSuccessorBaseTailPhaseSplitActiveBlockMixedCylinderConstructionGoal_of_coordinatized_activeBlock
    (hBuild :
      OddSuccessorBaseTailCoordinatizedPhaseSplitActiveBlockCylinderConstructionGoal) :
    OddSuccessorBaseTailPhaseSplitActiveBlockMixedCylinderConstructionGoal :=
  oddSuccessorBaseTailPhaseSplitActiveBlockMixedCylinderConstructionGoal_of_activeBlock
    (oddSuccessorBaseTailPhaseSplitActiveBlockCylinderConstructionGoal_of_coordinatized
      hBuild)

theorem oddSuccessorBaseTailPhaseSplitActiveBlockMixedCylinderConstructionGoal :
    OddSuccessorBaseTailPhaseSplitActiveBlockMixedCylinderConstructionGoal :=
  oddSuccessorBaseTailPhaseSplitActiveBlockMixedCylinderConstructionGoal_of_coordinatized_activeBlock
    oddSuccessorBaseTailCoordinatizedPhaseSplitActiveBlockCylinderConstructionGoal

theorem oddSuccessorBaseTailRawActiveBlockCylinderConstructionGoal_of_phaseSplit
    (hSplit : BaseTail.SuccessorPacketPhaseSplitPowerGoal)
    (hBuild : OddSuccessorBaseTailPhaseSplitActiveBlockCylinderConstructionGoal) :
    OddSuccessorBaseTailRawActiveBlockCylinderConstructionGoal := by
  intro b m T _inst hb5 _hmodd hm3 _hsmall hbase packets
    hlen htotal hpacketSum hpacketUnits hPrefix hT
  letI : NeZero (m ^ b) := ⟨pow_ne_zero b (NeZero.ne m)⟩
  rcases hbase with ⟨Dbase⟩
  have hPacketSplits :
      ∀ packet, packet ∈ packets →
        Nonempty (BaseTail.PacketPhaseSplit (m ^ b) m packet) := by
    intro packet hp
    exact
      hSplit (b := b) (m := m) (T := T) (packets := packets)
        (by omega)
        hm3 hT hlen htotal hpacketSum hpacketUnits packet hp
  exact
    hBuild hb5 hm3 Dbase packets hlen htotal
      hpacketSum hpacketUnits hPrefix hPacketSplits hT

theorem oddSuccessorBaseTailRawActiveBlockCylinderConstructionGoal :
    OddSuccessorBaseTailRawActiveBlockCylinderConstructionGoal :=
  oddSuccessorBaseTailRawActiveBlockCylinderConstructionGoal_of_phaseSplit
    BaseTail.successorPacketPhaseSplitPowerGoal
    oddSuccessorBaseTailPhaseSplitActiveBlockCylinderConstructionGoal

theorem oddSuccessorBaseTailActiveBlockCylinderConstructionGoal_of_raw
    (hRaw : OddSuccessorBaseTailRawActiveBlockCylinderConstructionGoal) :
    OddSuccessorBaseTailActiveBlockCylinderConstructionGoal := by
  intro b m T _inst hb5 hmodd hm3 hsmall hbase packets
    hlen htotal hpacketSum hpacketUnits hPrefix hT
  rcases hRaw hb5 hmodd hm3 hsmall hbase packets
      hlen htotal hpacketSum hpacketUnits hPrefix hT with
    ⟨Cyl, D, hOrdinary, hHamiltonian⟩
  refine ⟨Cyl, D, ?_⟩
  exact D.isCylinder_of_activeBlockData hOrdinary hHamiltonian (by omega)

theorem oddSuccessorBaseTailActiveBlockCylinderConstructionGoal :
    OddSuccessorBaseTailActiveBlockCylinderConstructionGoal :=
  oddSuccessorBaseTailActiveBlockCylinderConstructionGoal_of_raw
    oddSuccessorBaseTailRawActiveBlockCylinderConstructionGoal

def OddSuccessorBaseTailActiveBlockMixedCylinderConstructionGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m],
    5 ≤ b →
    Odd m → 3 ≤ m → m < b + T →
    StandardCayleySolved b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    (∀ packet, packet ∈ packets →
      ∀ q : Nat, 0 < q → q < packet.length →
        Nat.Coprime (packet.take q).sum m) →
    T = b + 1 →
    ∃ Cyl : BaseTail.Cylinder b m T packets,
      ∃ _D : BaseTail.ActiveBlockData Cyl,
      ∃ _Mix : BaseTail.MixedExpansionData Cyl,
        BaseTail.IsCylinder Cyl

theorem oddSuccessorBaseTailActiveBlockMixedCylinderConstructionGoal_of_phaseSplit
    (hSplit : BaseTail.SuccessorPacketPhaseSplitPowerGoal)
    (hBuild :
      OddSuccessorBaseTailPhaseSplitActiveBlockMixedCylinderConstructionGoal) :
    OddSuccessorBaseTailActiveBlockMixedCylinderConstructionGoal := by
  intro b m T _inst hb5 _hmodd hm3 _hsmall hbase packets
    hlen htotal hpacketSum hpacketUnits hPrefix hT
  letI : NeZero (m ^ b) := ⟨pow_ne_zero b (NeZero.ne m)⟩
  rcases hbase with ⟨Dbase⟩
  have hPacketSplits :
      ∀ packet, packet ∈ packets →
        Nonempty (BaseTail.PacketPhaseSplit (m ^ b) m packet) := by
    intro packet hp
    exact
      hSplit (b := b) (m := m) (T := T) (packets := packets)
        (by omega)
        hm3 hT hlen htotal hpacketSum hpacketUnits packet hp
  exact
    hBuild hb5 hm3 Dbase packets hlen htotal
      hpacketSum hpacketUnits hPrefix hPacketSplits hT

theorem oddSuccessorBaseTailActiveBlockMixedCylinderConstructionGoal_of_coordinatized_phaseSplit
    (hBuild :
      OddSuccessorBaseTailCoordinatizedPhaseSplitActiveBlockCylinderConstructionGoal) :
    OddSuccessorBaseTailActiveBlockMixedCylinderConstructionGoal :=
  oddSuccessorBaseTailActiveBlockMixedCylinderConstructionGoal_of_phaseSplit
    BaseTail.successorPacketPhaseSplitPowerGoal
    (oddSuccessorBaseTailPhaseSplitActiveBlockMixedCylinderConstructionGoal_of_coordinatized_activeBlock
      hBuild)

theorem oddSuccessorBaseTailActiveBlockMixedCylinderConstructionGoal :
    OddSuccessorBaseTailActiveBlockMixedCylinderConstructionGoal :=
  oddSuccessorBaseTailActiveBlockMixedCylinderConstructionGoal_of_coordinatized_phaseSplit
    oddSuccessorBaseTailCoordinatizedPhaseSplitActiveBlockCylinderConstructionGoal

def OddSuccessorBaseTailActiveBlockMixedExpansionGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m],
    5 ≤ b →
    Odd m → 3 ≤ m → m < b + T →
    StandardCayleySolved b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    (∀ packet, packet ∈ packets →
      ∀ q : Nat, 0 < q → q < packet.length →
        Nat.Coprime (packet.take q).sum m) →
    T = b + 1 →
    ∀ {Cyl : BaseTail.Cylinder b m T packets},
      BaseTail.IsCylinder Cyl →
      BaseTail.ActiveBlockData Cyl →
      BaseTail.MixedExpansionData Cyl

def OddSuccessorBaseTailActiveBlockMixedWitnessGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m],
    5 ≤ b →
    Odd m → 3 ≤ m → m < b + T →
    StandardCayleySolved b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    (∀ packet, packet ∈ packets →
      ∀ q : Nat, 0 < q → q < packet.length →
        Nat.Coprime (packet.take q).sum m) →
    T = b + 1 →
    ∀ {Cyl : BaseTail.Cylinder b m T packets},
      BaseTail.IsCylinder Cyl →
      BaseTail.ActiveBlockData Cyl →
      Nonempty (BaseTail.MixedLowerWitnessData Cyl)

theorem oddSuccessorBaseTailActiveBlockMixedExpansionGoal_of_witness
    (hWitness : OddSuccessorBaseTailActiveBlockMixedWitnessGoal) :
    OddSuccessorBaseTailActiveBlockMixedExpansionGoal := by
  intro b m T _inst hb5 hmodd hm3 hsmall hbase packets
    hlen htotal hpacketSum hpacketUnits hPrefix hT
    Cyl hCyl hBlock
  rcases hWitness hb5 hmodd hm3 hsmall hbase packets
      hlen htotal hpacketSum hpacketUnits hPrefix hT
      hCyl hBlock with
    ⟨W⟩
  exact BaseTail.mixedExpansionData_of_mixedLowerWitnessData
    W

theorem oddSuccessorBaseTailActiveBlockMixedCylinderConstructionGoal_of_activeBlock_mixedExpansion
    (hCyl : OddSuccessorBaseTailActiveBlockCylinderConstructionGoal)
    (hMix : OddSuccessorBaseTailActiveBlockMixedExpansionGoal) :
    OddSuccessorBaseTailActiveBlockMixedCylinderConstructionGoal := by
  intro b m T _inst hb5 hmodd hm3 hsmall hbase packets hlen htotal
    hpacketSum hpacketUnits hPrefix hT
  rcases hCyl hb5 hmodd hm3 hsmall hbase packets
      hlen htotal hpacketSum hpacketUnits hPrefix hT with
    ⟨Cyl, D, hCylValid⟩
  exact ⟨Cyl, D,
    hMix hb5 hmodd hm3 hsmall hbase packets
      hlen htotal hpacketSum hpacketUnits hPrefix hT
      hCylValid D,
    hCylValid⟩

def OddSuccessorBaseTailActiveBlockResidueRoundingGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m],
    5 ≤ b →
    Odd m → 3 ≤ m → m < b + T →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    (∀ packet, packet ∈ packets →
      ∀ q : Nat, 0 < q → q < packet.length →
        Nat.Coprime (packet.take q).sum m) →
    T = b + 1 →
    m ^ b > m * (b + T) * T →
    ∀ {Cyl : BaseTail.Cylinder b m T packets},
      BaseTail.IsCylinder Cyl →
      BaseTail.ActiveBlockData Cyl →
      (hT2 : 2 ≤ T) →
        BaseTail.HasFeasiblePrimitiveResidues hT2 Cyl

/--
The active-block residue-rounding problem in its sharpest local form.

The universal primitive residue pattern is already constructed from the
active-block degree formula in `BaseTailGeometry.lean`.  The remaining
rounding content is therefore exactly this: every row/column compatible
primitive residue specification admits a nonnegative count matrix satisfying
the active Hall cuts and those residues.
-/
def OddSuccessorBaseTailActiveBlockCompatibleResidueRoundingGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m],
    5 ≤ b →
    Odd m → 3 ≤ m → m < b + T →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    (∀ packet, packet ∈ packets →
      ∀ q : Nat, 0 < q → q < packet.length →
        Nat.Coprime (packet.take q).sum m) →
    T = b + 1 →
    m ^ b > m * (b + T) * T →
    ∀ {Cyl : BaseTail.Cylinder b m T packets},
      BaseTail.IsCylinder Cyl →
      BaseTail.ActiveBlockData Cyl →
      (hT2 : 2 ≤ T) →
      ∀ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
        R.RowCompatible Cyl.incidence →
        R.ColCompatible Cyl.incidence →
        (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) →
        (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
          IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) →
        ActiveHall.FeasibleWithResidues Cyl.incidence R

def OddSuccessorBaseTailActiveBlockMixedCompatibleResidueRoundingGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m],
    5 ≤ b →
    Odd m → 3 ≤ m → m < b + T →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    (∀ packet, packet ∈ packets →
      ∀ q : Nat, 0 < q → q < packet.length →
        Nat.Coprime (packet.take q).sum m) →
    T = b + 1 →
    m ^ b > m * (b + T) * T →
    ∀ {Cyl : BaseTail.Cylinder b m T packets},
      BaseTail.IsCylinder Cyl →
      BaseTail.ActiveBlockData Cyl →
      BaseTail.MixedExpansionData Cyl →
      (hT2 : 2 ≤ T) →
      ∀ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
        R.RowCompatible Cyl.incidence →
        R.ColCompatible Cyl.incidence →
        (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) →
        (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
          IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) →
        ActiveHall.FeasibleWithResidues Cyl.incidence R

def OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m],
    5 ≤ b →
    Odd m → 3 ≤ m → m < b + T →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    (∀ packet, packet ∈ packets →
      ∀ q : Nat, 0 < q → q < packet.length →
        Nat.Coprime (packet.take q).sum m) →
    T = b + 1 →
    m ^ b > m * (b + T) * T →
    ∀ {Cyl : BaseTail.Cylinder b m T packets},
      BaseTail.IsCylinder Cyl →
      BaseTail.ActiveBlockData Cyl →
      BaseTail.MixedExpansionData Cyl →
      (hT2 : 2 ≤ T) →
      ∀ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
        R.RowCompatible Cyl.incidence →
        R.ColCompatible Cyl.incidence →
        (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) →
        (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
          IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) →
        ∃ M : ActiveHall.CountMatrix Cyl.incidence,
          M.HasResidues R ∧
            ∀ U : Finset (Fin (b + T)), ∀ S : Finset (Fin T),
              U.Nonempty → U ≠ Finset.univ →
              S.Nonempty → S ≠ Finset.univ →
                T * M.cutMass U S ≤
                  S.card * (∑ c ∈ U, (Cyl.incidence).colorDegree c) +
                    m * (b + T) * min S.card (T - S.card)

/--
Generic count-matrix rounding boundary for the active Hall layer.

The base-tail data only supplies a concrete incidence structure and the error
scale `m * #colors`; the rounding theorem itself should not depend on packets,
cylinders, or Hamiltonian geometry.

This is retained only as an optional stronger interface.  The Worker-1
base-tail residuals below use the specialized mixed-cylinder controlled
rounding goal, since row/column residue compatibility alone is not enough to
construct a nonnegative count matrix with prescribed residues.
-/
def ActiveHallControlledResidueRoundingGoal : Prop :=
  ∀ {m T : Nat} [NeZero m] {X C : Type}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    (I : ActiveHall.Incidence T X C) →
    ∀ R : ActiveHall.ResidueSpec m T C,
      R.RowCompatible I →
      R.ColCompatible I →
      ∃ M : ActiveHall.CountMatrix I,
        M.HasResidues R ∧
          ∀ U : Finset C, ∀ S : Finset (Fin T),
            U.Nonempty → U ≠ Finset.univ →
            S.Nonempty → S ≠ Finset.univ →
              T * M.cutMass U S ≤
                S.card * (∑ c ∈ U, I.colorDegree c) +
                  m * Fintype.card C * min S.card (T - S.card)

/--
Large-margin form of controlled active-Hall residue rounding.

The base-tail geometry should only be responsible for producing an incidence
whose color degrees are much larger than the residue/error scale.  The
remaining rounding theorem is a pure finite arithmetic statement for
incidence count matrices.
-/
def ActiveHallLargeMarginControlledResidueRoundingGoal : Prop :=
  ∀ {m T : Nat} [NeZero m] {X C : Type}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    (I : ActiveHall.Incidence T X C) →
    0 < T →
    (∀ c : C, m * Fintype.card C * T < I.colorDegree c) →
    ∀ R : ActiveHall.ResidueSpec m T C,
      R.RowCompatible I →
      R.ColCompatible I →
      ∃ M : ActiveHall.CountMatrix I,
        M.HasResidues R ∧
          ∀ U : Finset C, ∀ S : Finset (Fin T),
            U.Nonempty → U ≠ Finset.univ →
            S.Nonempty → S ≠ Finset.univ →
              T * M.cutMass U S ≤
                S.card * (∑ c ∈ U, I.colorDegree c) +
                  m * Fintype.card C * min S.card (T - S.card)

theorem oddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal_of_activeHallControlled
    (hRound : ActiveHallControlledResidueRoundingGoal) :
    OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal := by
  intro b m T _inst _hb5 _hmodd _hm3 _hsmall packets _hlen _htotal
    _hpacketSum _hpacketUnits _hPrefix _hT _hSlack
    Cyl _hCyl _hBlock _hMix _hT2 R hRow hCol _hZero _hNumeric
  rcases hRound Cyl.incidence R hRow hCol with ⟨M, hResidues, hScaled⟩
  refine ⟨M, hResidues, ?_⟩
  intro U S hUne hUuniv hSne hSuniv
  simpa [Fintype.card_fin] using
    hScaled U S hUne hUuniv hSne hSuniv

theorem oddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal_of_largeMarginControlled
    (hRound : ActiveHallLargeMarginControlledResidueRoundingGoal) :
    OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal := by
  intro b m T _inst _hb5 _hmodd _hm3 _hsmall packets _hlen _htotal
    _hpacketSum _hpacketUnits _hPrefix _hT hSlack
    Cyl _hCyl hBlock _hMix hT2 R hRow hCol _hZero _hNumeric
  have hTpos : 0 < T := by omega
  have hLarge :
      ∀ c : Fin (b + T),
        m * Fintype.card (Fin (b + T)) * T <
          (Cyl.incidence).colorDegree c := by
    intro c
    have hScale : m * Fintype.card (Fin (b + T)) * T < m ^ b := by
      simpa [Fintype.card_fin] using hSlack
    exact hScale.trans_le (hBlock.active_degree_lower_bound c)
  rcases hRound Cyl.incidence hTpos hLarge R hRow hCol with
    ⟨M, hResidues, hScaled⟩
  refine ⟨M, hResidues, ?_⟩
  intro U S hUne hUuniv hSne hSuniv
  simpa [Fintype.card_fin] using
    hScaled U S hUne hUuniv hSne hSuniv

def OddSuccessorBaseTailActiveBlockPrimitiveLiftGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m],
    5 ≤ b →
    Odd m → 3 ≤ m → m < b + T →
    StandardCayleySolved b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    (∀ packet, packet ∈ packets →
      ∀ q : Nat, 0 < q → q < packet.length →
        Nat.Coprime (packet.take q).sum m) →
    T = b + 1 →
    m ^ b > m * (b + T) * T →
    ∀ {Cyl : BaseTail.Cylinder b m T packets}
      {A : BaseTail.ActiveSymboling Cyl},
      BaseTail.IsCylinder Cyl →
      BaseTail.ActiveBlockData Cyl →
      (hT2 : 2 ≤ T) →
      BaseTail.IsPrimitiveActiveSymboling hT2 A →
      StandardCayleySolved (b + T) m

theorem oddSuccessorBaseTailActiveBlockPrimitiveLiftGoal_of_primitiveActiveLift
    (hLift : OddSuccessorBaseTailPrimitiveActiveLiftGoal) :
    OddSuccessorBaseTailActiveBlockPrimitiveLiftGoal := by
  intro b m T _inst hb5 hmodd hm3 hsmall hbase packets
    hlen htotal hpacketSum hpacketUnits hPrefix hT hSlack
    Cyl A hCyl _hBlock hT2 hA
  exact hLift hb5 hmodd hm3 hsmall hbase packets
    hlen htotal hpacketSum hpacketUnits hPrefix hT hSlack
    hCyl hT2 hA

theorem oddSuccessorBaseTailActiveBlockPrimitiveLiftGoal_of_prefixLiftAssembly
    (hLift : BaseTail.PrimitiveActivePrefixLiftAssemblyGoal) :
    OddSuccessorBaseTailActiveBlockPrimitiveLiftGoal :=
  oddSuccessorBaseTailActiveBlockPrimitiveLiftGoal_of_primitiveActiveLift
    (oddSuccessorBaseTailPrimitiveActiveLiftGoal_of_prefixLiftAssembly hLift)

theorem oddSuccessorBaseTailActiveBlockPrimitiveLiftGoal_of_expandedColorDirHamiltonian
    (hHam : BaseTail.ExpandedColorDirColorHamiltonianGoal) :
    OddSuccessorBaseTailActiveBlockPrimitiveLiftGoal :=
  oddSuccessorBaseTailActiveBlockPrimitiveLiftGoal_of_primitiveActiveLift
    (oddSuccessorBaseTailPrimitiveActiveLiftGoal_of_expandedColorDirHamiltonian
      hHam)

theorem oddSuccessorBaseTailActiveBlockResidueRoundingGoal_of_compatible
    (hCompatible :
      OddSuccessorBaseTailActiveBlockCompatibleResidueRoundingGoal) :
    OddSuccessorBaseTailActiveBlockResidueRoundingGoal := by
  intro b m T _inst hb5 hmodd hm3 hsmall packets hlen htotal
    hpacketSum hpacketUnits hPrefix hT hSlack Cyl hCyl hBlock hT2
  exact
    BaseTail.feasiblePrimitiveResidues_of_successor_activeBlockData_feasible_compatible
      hb5 hT hmodd hBlock
      (hCompatible hb5 hmodd hm3 hsmall packets hlen htotal
        hpacketSum hpacketUnits hPrefix hT hSlack hCyl hBlock hT2)

theorem oddSuccessorBaseTailActiveBlockMixedCompatibleResidueRoundingGoal_of_controlled
    (hControlled :
      OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal) :
    OddSuccessorBaseTailActiveBlockMixedCompatibleResidueRoundingGoal := by
  intro b m T _inst hb5 hmodd hm3 hsmall packets hlen htotal
    hpacketSum hpacketUnits hPrefix hT hSlack Cyl hCyl hBlock hMix hT2
    R hRow hCol hZero hNumeric
  rcases hControlled hb5 hmodd hm3 hsmall packets hlen htotal
      hpacketSum hpacketUnits hPrefix hT hSlack hCyl hBlock hMix hT2
      R hRow hCol hZero hNumeric with
    ⟨M, hResidues, hScaled⟩
  exact
    hMix.feasibleWithResidues_of_scaled_error_le_slack
      (by omega : 0 < T) hSlack M hResidues hScaled

theorem oddSuccessorBaseTailActiveBlockMixedCompatibleResidueRoundingGoal_of_activeHallControlled
    (hRound : ActiveHallControlledResidueRoundingGoal) :
    OddSuccessorBaseTailActiveBlockMixedCompatibleResidueRoundingGoal :=
  oddSuccessorBaseTailActiveBlockMixedCompatibleResidueRoundingGoal_of_controlled
    (oddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal_of_activeHallControlled
      hRound)

theorem oddSuccessorBaseTailActiveBlockMixedCompatibleResidueRoundingGoal_of_largeMarginControlled
    (hRound : ActiveHallLargeMarginControlledResidueRoundingGoal) :
    OddSuccessorBaseTailActiveBlockMixedCompatibleResidueRoundingGoal :=
  oddSuccessorBaseTailActiveBlockMixedCompatibleResidueRoundingGoal_of_controlled
    (oddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal_of_largeMarginControlled
      hRound)

theorem oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_baseTailPieces
    (hCyl : OddSuccessorBaseTailCylinderConstructionGoal)
    (hRound : OddSuccessorBaseTailResidueRoundingGoal)
    (hLift : OddSuccessorBaseTailPrimitiveActiveLiftGoal) :
    OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal := by
  intro hHall b m T hb5 hmodd hm3 hsmall hbase
    packets hlen htotal hpacketSum hpacketUnits hPrefix hT hSlack
  letI : NeZero m := ⟨ne_of_gt (by omega : 0 < m)⟩
  rcases hCyl hb5 hmodd hm3 hsmall hbase packets
      hlen htotal hpacketSum hpacketUnits hPrefix hT with
    ⟨Cyl, hCylValid⟩
  have hT2 : 2 ≤ T := by omega
  have hResidues :
      BaseTail.HasFeasiblePrimitiveResidues hT2 Cyl :=
    hRound hb5 hmodd hm3 hsmall packets hlen htotal
      hpacketSum hpacketUnits hPrefix hT hSlack hCylValid hT2
  rcases
    BaseTail.primitiveActiveSymboling_of_feasiblePrimitiveResidues_and_hallRealization
      hHall hResidues with
    ⟨A, hA⟩
  exact hLift hb5 hmodd hm3 hsmall hbase packets hlen htotal
    hpacketSum hpacketUnits hPrefix hT hSlack hCylValid hT2 hA

theorem oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlockPieces
    (hCyl : OddSuccessorBaseTailActiveBlockCylinderConstructionGoal)
    (hRound : OddSuccessorBaseTailActiveBlockResidueRoundingGoal)
    (hLift : OddSuccessorBaseTailActiveBlockPrimitiveLiftGoal) :
    OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal := by
  intro hHall b m T hb5 hmodd hm3 hsmall hbase
    packets hlen htotal hpacketSum hpacketUnits hPrefix hT hSlack
  letI : NeZero m := ⟨ne_of_gt (by omega : 0 < m)⟩
  rcases hCyl hb5 hmodd hm3 hsmall hbase packets
      hlen htotal hpacketSum hpacketUnits hPrefix hT with
    ⟨Cyl, hBlock, hCylValid⟩
  have hT2 : 2 ≤ T := by omega
  have hResidues :
      BaseTail.HasFeasiblePrimitiveResidues hT2 Cyl :=
    hRound hb5 hmodd hm3 hsmall packets hlen htotal
      hpacketSum hpacketUnits hPrefix hT hSlack hCylValid hBlock hT2
  rcases
    BaseTail.primitiveActiveSymboling_of_feasiblePrimitiveResidues_and_hallRealization
      hHall hResidues with
    ⟨A, hA⟩
  exact hLift hb5 hmodd hm3 hsmall hbase packets hlen htotal
    hpacketSum hpacketUnits hPrefix hT hSlack hCylValid hBlock hT2 hA

theorem oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlockCompatiblePieces
    (hCyl : OddSuccessorBaseTailActiveBlockCylinderConstructionGoal)
    (hRound :
      OddSuccessorBaseTailActiveBlockCompatibleResidueRoundingGoal)
    (hLift : OddSuccessorBaseTailActiveBlockPrimitiveLiftGoal) :
    OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal :=
  oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlockPieces
    hCyl
    (oddSuccessorBaseTailActiveBlockResidueRoundingGoal_of_compatible hRound)
    hLift

theorem oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlockMixedCompatiblePieces
    (hCyl : OddSuccessorBaseTailActiveBlockMixedCylinderConstructionGoal)
    (hRound :
      OddSuccessorBaseTailActiveBlockMixedCompatibleResidueRoundingGoal)
    (hLift : OddSuccessorBaseTailActiveBlockPrimitiveLiftGoal) :
    OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal := by
  intro hHall b m T hb5 hmodd hm3 hsmall hbase
    packets hlen htotal hpacketSum hpacketUnits hPrefix hT hSlack
  letI : NeZero m := ⟨ne_of_gt (by omega : 0 < m)⟩
  rcases hCyl hb5 hmodd hm3 hsmall hbase packets
      hlen htotal hpacketSum hpacketUnits hPrefix hT with
    ⟨Cyl, hBlock, hMix, hCylValid⟩
  have hT2 : 2 ≤ T := by omega
  have hResidues :
      BaseTail.HasFeasiblePrimitiveResidues hT2 Cyl :=
    BaseTail.feasiblePrimitiveResidues_of_successor_activeBlockData_feasible_compatible
      hb5 hT hmodd hBlock
      (hRound hb5 hmodd hm3 hsmall packets hlen htotal
        hpacketSum hpacketUnits hPrefix hT hSlack hCylValid hBlock hMix hT2)
  rcases
    BaseTail.primitiveActiveSymboling_of_feasiblePrimitiveResidues_and_hallRealization
      hHall hResidues with
    ⟨A, hA⟩
  exact hLift hb5 hmodd hm3 hsmall hbase packets hlen htotal
    hpacketSum hpacketUnits hPrefix hT hSlack hCylValid hBlock hT2 hA

theorem oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlockMixedControlledPieces
    (hCyl : OddSuccessorBaseTailActiveBlockMixedCylinderConstructionGoal)
    (hRound :
      OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal)
    (hLift : OddSuccessorBaseTailActiveBlockPrimitiveLiftGoal) :
    OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal :=
  oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlockMixedCompatiblePieces
    hCyl
    (oddSuccessorBaseTailActiveBlockMixedCompatibleResidueRoundingGoal_of_controlled
      hRound)
    hLift

theorem oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_closedCylinder_controlled_prefix
    (hRound :
      OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal)
    (hLift : BaseTail.PrimitiveActivePrefixLiftAssemblyGoal) :
    OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal :=
  oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlockMixedControlledPieces
    oddSuccessorBaseTailActiveBlockMixedCylinderConstructionGoal
    hRound
    (oddSuccessorBaseTailActiveBlockPrimitiveLiftGoal_of_prefixLiftAssembly
      hLift)

theorem oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlock_mixedExpansion_controlled_prefix
    (hCyl : OddSuccessorBaseTailActiveBlockCylinderConstructionGoal)
    (hMix : OddSuccessorBaseTailActiveBlockMixedExpansionGoal)
    (hRound :
      OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal)
    (hLift : BaseTail.PrimitiveActivePrefixLiftAssemblyGoal) :
    OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal :=
  oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlockMixedControlledPieces
    (oddSuccessorBaseTailActiveBlockMixedCylinderConstructionGoal_of_activeBlock_mixedExpansion
      hCyl hMix)
    hRound
    (oddSuccessorBaseTailActiveBlockPrimitiveLiftGoal_of_prefixLiftAssembly
      hLift)

theorem oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlock_mixedExpansion_activeHallControlled_prefix
    (hCyl : OddSuccessorBaseTailActiveBlockCylinderConstructionGoal)
    (hMix : OddSuccessorBaseTailActiveBlockMixedExpansionGoal)
    (hRound : ActiveHallControlledResidueRoundingGoal)
    (hLift : BaseTail.PrimitiveActivePrefixLiftAssemblyGoal) :
    OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal :=
  oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlock_mixedExpansion_controlled_prefix
    hCyl
    hMix
    (oddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal_of_activeHallControlled
      hRound)
    hLift

theorem oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_rawActiveBlock_mixedExpansion_activeHallControlled_prefix
    (hCyl : OddSuccessorBaseTailRawActiveBlockCylinderConstructionGoal)
    (hMix : OddSuccessorBaseTailActiveBlockMixedExpansionGoal)
    (hRound : ActiveHallControlledResidueRoundingGoal)
    (hLift : BaseTail.PrimitiveActivePrefixLiftAssemblyGoal) :
    OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal :=
  oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlock_mixedExpansion_activeHallControlled_prefix
    (oddSuccessorBaseTailActiveBlockCylinderConstructionGoal_of_raw hCyl)
    hMix
    hRound
    hLift

theorem oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_rawActiveBlock_mixedWitness_activeHallControlled_prefix
    (hCyl : OddSuccessorBaseTailRawActiveBlockCylinderConstructionGoal)
    (hMix : OddSuccessorBaseTailActiveBlockMixedWitnessGoal)
    (hRound : ActiveHallControlledResidueRoundingGoal)
    (hLift : BaseTail.PrimitiveActivePrefixLiftAssemblyGoal) :
    OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal :=
  oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_rawActiveBlock_mixedExpansion_activeHallControlled_prefix
    hCyl
    (oddSuccessorBaseTailActiveBlockMixedExpansionGoal_of_witness hMix)
    hRound
    hLift

theorem oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_core
    (hCore : OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal) :
    OddSuccessorSmallModulusBaseTailGeometryFromHallGoal := by
  intro hHall b m T hb5 hmodd hm3 hsmall hbase
    packets hlen htotal hpacketSum hpacketUnits hT hSlack
  have hPrefix :
      ∀ packet, packet ∈ packets →
        ∀ q : Nat, 0 < q → q < packet.length →
          Nat.Coprime (packet.take q).sum m :=
    BaseTail.successorPacketProperPrefixUnitsGoal
      hm3 hT hlen htotal hpacketSum hpacketUnits
  exact hCore hHall hb5 hmodd hm3 hsmall hbase
    packets hlen htotal hpacketSum hpacketUnits hPrefix hT hSlack

theorem oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_activeBlock_mixedExpansion_controlled_prefix
    (hCyl : OddSuccessorBaseTailActiveBlockCylinderConstructionGoal)
    (hMix : OddSuccessorBaseTailActiveBlockMixedExpansionGoal)
    (hRound :
      OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal)
    (hLift : BaseTail.PrimitiveActivePrefixLiftAssemblyGoal) :
    OddSuccessorSmallModulusBaseTailGeometryFromHallGoal :=
  oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_core
    (oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlock_mixedExpansion_controlled_prefix
      hCyl hMix hRound hLift)

theorem oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_closedCylinder_controlled_prefix
    (hRound :
      OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal)
    (hLift : BaseTail.PrimitiveActivePrefixLiftAssemblyGoal) :
    OddSuccessorSmallModulusBaseTailGeometryFromHallGoal :=
  oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_core
    (oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_closedCylinder_controlled_prefix
      hRound hLift)

theorem oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_largeMarginControlled_prefix
    (hRound : ActiveHallLargeMarginControlledResidueRoundingGoal)
    (hLift : BaseTail.PrimitiveActivePrefixLiftAssemblyGoal) :
    OddSuccessorSmallModulusBaseTailGeometryFromHallGoal :=
  oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_closedCylinder_controlled_prefix
    (oddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal_of_largeMarginControlled
      hRound)
    hLift

theorem oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_activeBlock_mixedExpansion_activeHallControlled_prefix
    (hCyl : OddSuccessorBaseTailActiveBlockCylinderConstructionGoal)
    (hMix : OddSuccessorBaseTailActiveBlockMixedExpansionGoal)
    (hRound : ActiveHallControlledResidueRoundingGoal)
    (hLift : BaseTail.PrimitiveActivePrefixLiftAssemblyGoal) :
    OddSuccessorSmallModulusBaseTailGeometryFromHallGoal :=
  oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_core
    (oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlock_mixedExpansion_activeHallControlled_prefix
      hCyl hMix hRound hLift)

theorem oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_rawActiveBlock_mixedExpansion_activeHallControlled_prefix
    (hCyl : OddSuccessorBaseTailRawActiveBlockCylinderConstructionGoal)
    (hMix : OddSuccessorBaseTailActiveBlockMixedExpansionGoal)
    (hRound : ActiveHallControlledResidueRoundingGoal)
    (hLift : BaseTail.PrimitiveActivePrefixLiftAssemblyGoal) :
    OddSuccessorSmallModulusBaseTailGeometryFromHallGoal :=
  oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_core
    (oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_rawActiveBlock_mixedExpansion_activeHallControlled_prefix
      hCyl hMix hRound hLift)

theorem oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_rawActiveBlock_mixedWitness_activeHallControlled_prefix
    (hCyl : OddSuccessorBaseTailRawActiveBlockCylinderConstructionGoal)
    (hMix : OddSuccessorBaseTailActiveBlockMixedWitnessGoal)
    (hRound : ActiveHallControlledResidueRoundingGoal)
    (hLift : BaseTail.PrimitiveActivePrefixLiftAssemblyGoal) :
    OddSuccessorSmallModulusBaseTailGeometryFromHallGoal :=
  oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_core
    (oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_rawActiveBlock_mixedWitness_activeHallControlled_prefix
      hCyl hMix hRound hLift)

def OddSuccessorBaseTailWorker1ResidualGoal : Prop :=
  OddSuccessorBaseTailRawActiveBlockCylinderConstructionGoal ∧
  OddSuccessorBaseTailActiveBlockMixedWitnessGoal ∧
  OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal ∧
  BaseTail.PrimitiveActivePrefixLiftAssemblyGoal

theorem oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_worker1Residuals
    (h : OddSuccessorBaseTailWorker1ResidualGoal) :
    OddSuccessorSmallModulusBaseTailGeometryFromHallGoal := by
  rcases h with ⟨hCyl, hMix, hRound, hLift⟩
  exact
    oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_core
      (oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlock_mixedExpansion_controlled_prefix
        (oddSuccessorBaseTailActiveBlockCylinderConstructionGoal_of_raw hCyl)
        (oddSuccessorBaseTailActiveBlockMixedExpansionGoal_of_witness hMix)
        hRound
        hLift)

def OddSuccessorBaseTailWorker1PhaseResidualGoal : Prop :=
  BaseTail.PacketPhaseSplitLengthTwoPowerGoal ∧
  BaseTail.PacketPhaseSplitLengthThreePowerGoal ∧
  OddSuccessorBaseTailPhaseSplitActiveBlockCylinderConstructionGoal ∧
  OddSuccessorBaseTailActiveBlockMixedWitnessGoal ∧
  OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal ∧
  BaseTail.PrimitiveActivePrefixLiftAssemblyGoal

theorem oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_worker1PhaseResiduals
    (h : OddSuccessorBaseTailWorker1PhaseResidualGoal) :
    OddSuccessorSmallModulusBaseTailGeometryFromHallGoal := by
  rcases h with ⟨hSplit2, hSplit3, hCyl, hMix, hRound, hLift⟩
  exact
    oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_worker1Residuals
      ⟨oddSuccessorBaseTailRawActiveBlockCylinderConstructionGoal_of_phaseSplit
          (BaseTail.successorPacketPhaseSplitPowerGoal_of_lengthTwoThreePower
            hSplit2 hSplit3)
          hCyl,
        hMix, hRound, hLift⟩

def OddSuccessorBaseTailWorker1PhaseMixedResidualGoal : Prop :=
  BaseTail.PacketPhaseSplitLengthTwoPowerGoal ∧
  BaseTail.PacketPhaseSplitLengthThreePowerGoal ∧
  OddSuccessorBaseTailPhaseSplitActiveBlockMixedCylinderConstructionGoal ∧
  OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal ∧
  BaseTail.PrimitiveActivePrefixLiftAssemblyGoal

theorem oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_worker1PhaseMixedResiduals
    (h : OddSuccessorBaseTailWorker1PhaseMixedResidualGoal) :
    OddSuccessorSmallModulusBaseTailGeometryFromHallGoal := by
  rcases h with ⟨hSplit2, hSplit3, hCylMix, hRound, hLift⟩
  exact
    oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_core
      (oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlockMixedControlledPieces
        (oddSuccessorBaseTailActiveBlockMixedCylinderConstructionGoal_of_phaseSplit
          (BaseTail.successorPacketPhaseSplitPowerGoal_of_lengthTwoThreePower
            hSplit2 hSplit3)
          hCylMix)
        hRound
        (oddSuccessorBaseTailActiveBlockPrimitiveLiftGoal_of_prefixLiftAssembly
          hLift))

def OddSuccessorBaseTailWorker1IntervalMixedResidualGoal : Prop :=
  BaseTail.PacketPhaseIntervalPowerConstructionGoal ∧
  OddSuccessorBaseTailPhaseSplitActiveBlockMixedCylinderConstructionGoal ∧
  OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal ∧
  BaseTail.PrimitiveActivePrefixLiftAssemblyGoal

theorem oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_worker1IntervalMixedResiduals
    (h : OddSuccessorBaseTailWorker1IntervalMixedResidualGoal) :
    OddSuccessorSmallModulusBaseTailGeometryFromHallGoal := by
  rcases h with ⟨hInterval, hCylMix, hRound, hLift⟩
  exact
    oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_worker1PhaseMixedResiduals
      ⟨BaseTail.packetPhaseSplitLengthTwoPowerGoal_of_intervalPower hInterval,
        BaseTail.packetPhaseSplitLengthThreePowerGoal_of_intervalPower hInterval,
        hCylMix, hRound, hLift⟩

def OddSuccessorBaseTailWorker1SkewMixedResidualGoal : Prop :=
  BaseTail.PacketPhaseSkewSingleCycleConstructionGoal ∧
  OddSuccessorBaseTailPhaseSplitActiveBlockMixedCylinderConstructionGoal ∧
  OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal ∧
  BaseTail.PrimitiveActivePrefixLiftAssemblyGoal

theorem oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_worker1SkewMixedResiduals
    (h : OddSuccessorBaseTailWorker1SkewMixedResidualGoal) :
    OddSuccessorSmallModulusBaseTailGeometryFromHallGoal := by
  rcases h with ⟨hSkew, hCylMix, hRound, hLift⟩
  exact
    oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_worker1IntervalMixedResiduals
      ⟨BaseTail.packetPhaseIntervalPowerConstructionGoal_of_skewSingleCycle
          hSkew,
        hCylMix, hRound, hLift⟩

def OddSuccessorBaseTailWorker1ClosedPacketMixedResidualGoal : Prop :=
  OddSuccessorBaseTailPhaseSplitActiveBlockMixedCylinderConstructionGoal ∧
  OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal ∧
  BaseTail.PrimitiveActivePrefixLiftAssemblyGoal

theorem oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_worker1ClosedPacketMixedResiduals
    (h : OddSuccessorBaseTailWorker1ClosedPacketMixedResidualGoal) :
    OddSuccessorSmallModulusBaseTailGeometryFromHallGoal := by
  rcases h with ⟨hCylMix, hRound, hLift⟩
  exact
    oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_worker1PhaseMixedResiduals
      ⟨BaseTail.packetPhaseSplitLengthTwoPowerGoal,
        BaseTail.packetPhaseSplitLengthThreePowerGoal,
        hCylMix, hRound, hLift⟩

def OddSuccessorBaseTailWorker1ClosedPacketMixedHamiltonianResidualGoal : Prop :=
  OddSuccessorBaseTailPhaseSplitActiveBlockMixedCylinderConstructionGoal ∧
  OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal ∧
  BaseTail.ExpandedColorDirColorHamiltonianGoal

def OddSuccessorBaseTailWorker1ClosedCylinderResidualGoal : Prop :=
  OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal ∧
  BaseTail.PrimitiveActivePrefixLiftAssemblyGoal

def OddSuccessorBaseTailWorker1LargeMarginResidualGoal : Prop :=
  ActiveHallLargeMarginControlledResidueRoundingGoal ∧
  BaseTail.PrimitiveActivePrefixLiftAssemblyGoal

theorem oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_worker1ClosedCylinderResiduals
    (h : OddSuccessorBaseTailWorker1ClosedCylinderResidualGoal) :
    OddSuccessorSmallModulusBaseTailGeometryFromHallGoal := by
  rcases h with ⟨hRound, hLift⟩
  exact
    oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_closedCylinder_controlled_prefix
      hRound hLift

theorem oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_worker1LargeMarginResiduals
    (h : OddSuccessorBaseTailWorker1LargeMarginResidualGoal) :
    OddSuccessorSmallModulusBaseTailGeometryFromHallGoal := by
  rcases h with ⟨hRound, hLift⟩
  exact
    oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_largeMarginControlled_prefix
      hRound hLift

theorem oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_worker1ClosedPacketMixedHamiltonianResiduals
    (h : OddSuccessorBaseTailWorker1ClosedPacketMixedHamiltonianResidualGoal) :
    OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal := by
  rcases h with ⟨hCylMix, hRound, hHam⟩
  exact
    oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlockMixedControlledPieces
      (oddSuccessorBaseTailActiveBlockMixedCylinderConstructionGoal_of_phaseSplit
        BaseTail.successorPacketPhaseSplitPowerGoal
        hCylMix)
      hRound
      (oddSuccessorBaseTailActiveBlockPrimitiveLiftGoal_of_expandedColorDirHamiltonian
        hHam)

theorem oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_worker1ClosedPacketMixedHamiltonianResiduals
    (h : OddSuccessorBaseTailWorker1ClosedPacketMixedHamiltonianResidualGoal) :
    OddSuccessorSmallModulusBaseTailGeometryFromHallGoal :=
  oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_core
    (oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_worker1ClosedPacketMixedHamiltonianResiduals
      h)

theorem oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_coreAdd
    (hLift : OddCoreSmallModulusSlackPacketLiftAddGoal) :
    OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal := by
  intro _hHall b m T hb5 hmodd hm3 hsmall hbase
    packets hlen htotal hpacketSum hpacketUnits _hPrefix hT hSlack
  have hdodd : Odd (b + T) := by
    rw [hT]
    exact ⟨b, by omega⟩
  have hd11 : 11 ≤ b + T := by omega
  have hTgt : T > b := by omega
  exact hLift
    (d := b + T) (m := m) (b := b) (T := T)
    hdodd hd11 hmodd hm3 hsmall hbase packets
    hlen htotal hpacketSum hpacketUnits rfl hTgt hSlack

def OddSuccessorSmallModulusBaseTailGeometryFromHoffmanGoal : Prop :=
  ActiveHall.HoffmanOrderedSDRGoal.{0, 0} →
    OddSuccessorSmallModulusSlackPacketLiftAddGoal

def OddSuccessorSmallModulusBaseTailGeometryExactEdgeColoringGoal : Prop :=
  OddSuccessorSmallModulusBaseTailGeometryFromHallGoal ∧
  ActiveHall.FiniteHoffman.ExactEdgeColoringGoal.{0, 0}

def OddSuccessorSmallModulusBaseTailGeometryRawEdgeColoringGoal : Prop :=
  OddSuccessorSmallModulusBaseTailGeometryFromHallGoal ∧
  ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal.{0, 0}

theorem oddSuccessorSmallModulusSlackPacketLiftAddGoal_of_baseTailGeometryFromHall
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hHall : ActiveHall.HallRealizationGoal.{0, 0}) :
    OddSuccessorSmallModulusSlackPacketLiftAddGoal :=
  hGeom hHall

theorem oddSuccessorSmallModulusSlackPacketLiftAddGoal_of_baseTailGeometryFromHoffman
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHoffmanGoal)
    (hHoffman : ActiveHall.HoffmanOrderedSDRGoal.{0, 0}) :
    OddSuccessorSmallModulusSlackPacketLiftAddGoal :=
  hGeom hHoffman

theorem oddSuccessorSmallModulusSlackPacketLiftAddGoal_of_baseTailGeometryFromHall_and_hoffman
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hHoffman : ActiveHall.HoffmanOrderedSDRGoal.{0, 0}) :
    OddSuccessorSmallModulusSlackPacketLiftAddGoal :=
  hGeom (ActiveHall.hallRealizationGoal_of_hoffmanOrderedSDR hHoffman)

theorem oddSuccessorSmallModulusSlackPacketLiftAddGoal_of_baseTailGeometryFromExactEdgeColoring
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hEdge : ActiveHall.FiniteHoffman.ExactEdgeColoringGoal.{0, 0}) :
    OddSuccessorSmallModulusSlackPacketLiftAddGoal :=
  hGeom (ActiveHall.hallRealizationGoal_of_exactEdgeColoring hEdge)

theorem oddSuccessorSmallModulusSlackPacketLiftAddGoal_of_baseTailGeometryExactEdgeColoring
    (hBlocks : OddSuccessorSmallModulusBaseTailGeometryExactEdgeColoringGoal) :
    OddSuccessorSmallModulusSlackPacketLiftAddGoal :=
  oddSuccessorSmallModulusSlackPacketLiftAddGoal_of_baseTailGeometryFromExactEdgeColoring
    hBlocks.1 hBlocks.2

theorem oddSuccessorSmallModulusSlackPacketLiftAddGoal_of_baseTailGeometryFromRawEdgeColoring
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hRaw : ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal.{0, 0}) :
    OddSuccessorSmallModulusSlackPacketLiftAddGoal :=
  oddSuccessorSmallModulusSlackPacketLiftAddGoal_of_baseTailGeometryFromExactEdgeColoring
    hGeom (ActiveHall.FiniteHoffman.exactEdgeColoringGoal_of_raw hRaw)

theorem oddSuccessorSmallModulusSlackPacketLiftAddGoal_of_baseTailGeometryRawEdgeColoring
    (hBlocks : OddSuccessorSmallModulusBaseTailGeometryRawEdgeColoringGoal) :
    OddSuccessorSmallModulusSlackPacketLiftAddGoal :=
  oddSuccessorSmallModulusSlackPacketLiftAddGoal_of_baseTailGeometryFromRawEdgeColoring
    hBlocks.1 hBlocks.2

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

theorem oddSuccessorSmallModulusBaseTailGoal_of_baseTailGeometryFromHall
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hHall : ActiveHall.HallRealizationGoal.{0, 0}) :
    OddSuccessorSmallModulusBaseTailGoal :=
  oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd
    (oddSuccessorSmallModulusSlackPacketLiftAddGoal_of_baseTailGeometryFromHall
      hGeom hHall)

theorem oddSuccessorSmallModulusBaseTailGoal_of_baseTailGeometryFromHoffman
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHoffmanGoal)
    (hHoffman : ActiveHall.HoffmanOrderedSDRGoal.{0, 0}) :
    OddSuccessorSmallModulusBaseTailGoal :=
  oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd
    (oddSuccessorSmallModulusSlackPacketLiftAddGoal_of_baseTailGeometryFromHoffman
      hGeom hHoffman)

theorem oddSuccessorSmallModulusBaseTailGoal_of_baseTailGeometryFromHall_and_hoffman
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hHoffman : ActiveHall.HoffmanOrderedSDRGoal.{0, 0}) :
    OddSuccessorSmallModulusBaseTailGoal :=
  oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd
    (oddSuccessorSmallModulusSlackPacketLiftAddGoal_of_baseTailGeometryFromHall_and_hoffman
      hGeom hHoffman)

theorem oddSuccessorSmallModulusBaseTailGoal_of_baseTailGeometryFromExactEdgeColoring
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hEdge : ActiveHall.FiniteHoffman.ExactEdgeColoringGoal.{0, 0}) :
    OddSuccessorSmallModulusBaseTailGoal :=
  oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd
    (oddSuccessorSmallModulusSlackPacketLiftAddGoal_of_baseTailGeometryFromExactEdgeColoring
      hGeom hEdge)

theorem oddSuccessorSmallModulusBaseTailGoal_of_baseTailGeometryExactEdgeColoring
    (hBlocks : OddSuccessorSmallModulusBaseTailGeometryExactEdgeColoringGoal) :
    OddSuccessorSmallModulusBaseTailGoal :=
  oddSuccessorSmallModulusBaseTailGoal_of_baseTailGeometryFromExactEdgeColoring
    hBlocks.1 hBlocks.2

theorem oddSuccessorSmallModulusBaseTailGoal_of_baseTailGeometryFromRawEdgeColoring
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hRaw : ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal.{0, 0}) :
    OddSuccessorSmallModulusBaseTailGoal :=
  oddSuccessorSmallModulusBaseTailGoal_of_baseTailGeometryFromExactEdgeColoring
    hGeom (ActiveHall.FiniteHoffman.exactEdgeColoringGoal_of_raw hRaw)

theorem oddSuccessorSmallModulusBaseTailGoal_of_baseTailGeometryRawEdgeColoring
    (hBlocks : OddSuccessorSmallModulusBaseTailGeometryRawEdgeColoringGoal) :
    OddSuccessorSmallModulusBaseTailGoal :=
  oddSuccessorSmallModulusBaseTailGoal_of_baseTailGeometryFromRawEdgeColoring
    hBlocks.1 hBlocks.2

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

def OddCoreHighModulusReturnTailOrbitTrellisBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal ∧
  PrefixCountFirstHitReturnTailMonodromyOrbitGoal

def OddCoreHighModulusReturnTailClosedTrellisBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal

def OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal ∧
  PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal

def OddCoreHighModulusReturnTailTriangularBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  PrefixCountFirstHitReturnTailTriangularCocycleBlocksGoal

def OddCoreHighModulusReturnTailTriangularTrellisBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal ∧
  PrefixCountFirstHitReturnTailTriangularCocycleBlocksGoal

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

def OddModulusToriV4ReturnTailOrbitTrellisBlocksGoal : Prop :=
  OddCoreHighModulusReturnTailOrbitTrellisBlocksGoal ∧
  OddSuccessorSmallModulusBaseTailGoal

def OddModulusToriV4ReturnTailClosedTrellisBlocksGoal : Prop :=
  OddCoreHighModulusReturnTailClosedTrellisBlocksGoal ∧
  OddSuccessorSmallModulusBaseTailGoal

def OddModulusToriV4ReturnTailClosedFullSupportTrellisBlocksGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  OddSuccessorSmallModulusBaseTailGoal

def OddModulusToriV4ReturnTailClosedFullSupportTrellisGeometryEdgeBlocksGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  OddSuccessorSmallModulusBaseTailGeometryExactEdgeColoringGoal

def OddModulusToriV4ReturnTailClosedFullSupportTrellisGeometryRawEdgeBlocksGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  OddSuccessorSmallModulusBaseTailGeometryRawEdgeColoringGoal

def OddModulusToriV4ReturnTailTriangularBlocksGoal : Prop :=
  OddCoreHighModulusReturnTailTriangularBlocksGoal ∧
  OddSuccessorSmallModulusBaseTailGoal

def OddModulusToriV4ReturnTailTriangularTrellisBlocksGoal : Prop :=
  OddCoreHighModulusReturnTailTriangularTrellisBlocksGoal ∧
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

def OddModulusToriV4ReturnTailOrbitTrellisAddBlocksGoal : Prop :=
  OddCoreHighModulusReturnTailOrbitTrellisBlocksGoal ∧
  OddSuccessorSmallModulusSlackPacketLiftAddGoal

def OddModulusToriV4ReturnTailClosedTrellisAddBlocksGoal : Prop :=
  OddCoreHighModulusReturnTailClosedTrellisBlocksGoal ∧
  OddSuccessorSmallModulusSlackPacketLiftAddGoal

def OddModulusToriV4ReturnTailClosedFullSupportTrellisAddBlocksGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  OddSuccessorSmallModulusSlackPacketLiftAddGoal

def OddModulusToriV4ReturnTailTriangularTrellisAddBlocksGoal : Prop :=
  OddCoreHighModulusReturnTailTriangularTrellisBlocksGoal ∧
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

theorem oddCoreHighModulusReturnTailOrbitBlocksGoal_of_trellis
    (hBlocks : OddCoreHighModulusReturnTailOrbitTrellisBlocksGoal) :
    OddCoreHighModulusReturnTailOrbitBlocksGoal :=
  ⟨PrefixCount.ordinaryQge2SignedSeedProperCutClosureGoal_of_signedTrellisHoffman
      hBlocks.1,
    hBlocks.2⟩

theorem oddCoreHighModulusReturnTailOrbitTrellisBlocksGoal_of_closedTrellis
    (hBlocks : OddCoreHighModulusReturnTailClosedTrellisBlocksGoal) :
    OddCoreHighModulusReturnTailOrbitTrellisBlocksGoal :=
  ⟨hBlocks, prefixCountFirstHitReturnTailMonodromyOrbitGoal⟩

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailClosedTrellis_blocks
    (hBlocks : OddCoreHighModulusReturnTailClosedTrellisBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailOrbit_blocks
    (oddCoreHighModulusReturnTailOrbitBlocksGoal_of_trellis
      (oddCoreHighModulusReturnTailOrbitTrellisBlocksGoal_of_closedTrellis
        hBlocks))

theorem oddCoreHighModulusReturnTailClosedTrellisBlocksGoal_of_fullSupport
    (hBlocks : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal) :
    OddCoreHighModulusReturnTailClosedTrellisBlocksGoal :=
  PrefixCount.ordinaryQge2SignedTrellisHoffmanGoal_of_fullSupport
    hBlocks.1 hBlocks.2

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailClosedFullSupportTrellis_blocks
    (hBlocks : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailClosedTrellis_blocks
    (oddCoreHighModulusReturnTailClosedTrellisBlocksGoal_of_fullSupport hBlocks)

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailOrbitTrellis_blocks
    (hBlocks : OddCoreHighModulusReturnTailOrbitTrellisBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailOrbit_blocks
    (oddCoreHighModulusReturnTailOrbitBlocksGoal_of_trellis hBlocks)

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailOrbitTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailOrbitTrellis_blocks
    ⟨hQge2Trellis, hOrbit⟩

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

theorem oddCoreHighModulusReturnTailTriangularBlocksGoal_of_trellis
    (hBlocks : OddCoreHighModulusReturnTailTriangularTrellisBlocksGoal) :
    OddCoreHighModulusReturnTailTriangularBlocksGoal :=
  ⟨PrefixCount.ordinaryQge2SignedSeedProperCutClosureGoal_of_signedTrellisHoffman
      hBlocks.1,
    hBlocks.2⟩

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailTriangular_blocks
    (hBlocks : OddCoreHighModulusReturnTailTriangularBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailOrbit
    hBlocks.1
    (prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_triangularCocycleBlocks
      hBlocks.2)

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailTriangular
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hTri : PrefixCountFirstHitReturnTailTriangularGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailTriangular_blocks
    ⟨hQge2Proper, ⟨hTri, hUnit⟩⟩

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailTriangularTrellis_blocks
    (hBlocks : OddCoreHighModulusReturnTailTriangularTrellisBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailTriangular_blocks
    (oddCoreHighModulusReturnTailTriangularBlocksGoal_of_trellis hBlocks)

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailTriangularTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hTri : PrefixCountFirstHitReturnTailTriangularGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailTriangularTrellis_blocks
    ⟨hQge2Trellis, ⟨hTri, hUnit⟩⟩

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailIncrementTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hInc : PrefixCountFirstHitReturnTailIncrementDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailTriangularTrellis
    hQge2Trellis
    (prefixCountFirstHitReturnTailTriangularGoal_of_incrementDependsOnTake
      hInc)
    hUnit

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailFiberIncrementTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hFiber : PrefixCountFirstHitReturnFiberIncrementDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailIncrementTrellis
    hQge2Trellis
    (prefixCountFirstHitReturnTailIncrementDependsOnTakeGoal_of_fiber
      hFiber)
    hUnit

theorem oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailHitConditionTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hHit : PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailFiberIncrementTrellis
    hQge2Trellis
    (prefixCountFirstHitReturnFiberIncrementDependsOnTakeGoal_of_hitCondition
      hHit)
    hUnit

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

theorem oddSuccessorClosureGoal_of_v4_returnTailOrbitTrellis_blocks
    (hBlocks : OddModulusToriV4ReturnTailOrbitTrellisBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailOrbitTrellis_blocks
      hBlocks.1)
    hBlocks.2

theorem oddSuccessorClosureGoal_of_v4_returnTailClosedTrellis_blocks
    (hBlocks : OddModulusToriV4ReturnTailClosedTrellisBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailClosedTrellis_blocks
      hBlocks.1)
    hBlocks.2

theorem oddSuccessorClosureGoal_of_v4_returnTailClosedFullSupportTrellis_blocks
    (hBlocks : OddModulusToriV4ReturnTailClosedFullSupportTrellisBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailClosedFullSupportTrellis_blocks
      hBlocks.1)
    hBlocks.2

theorem oddSuccessorClosureGoal_of_v4_returnTailClosedFullSupportTrellisGeometryEdge_blocks
    (hBlocks :
      OddModulusToriV4ReturnTailClosedFullSupportTrellisGeometryEdgeBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_returnTailClosedFullSupportTrellis_blocks
    ⟨hBlocks.1,
      oddSuccessorSmallModulusBaseTailGoal_of_baseTailGeometryExactEdgeColoring
        hBlocks.2⟩

theorem oddSuccessorClosureGoal_of_v4_returnTailClosedFullSupportTrellisGeometryRawEdge_blocks
    (hBlocks :
      OddModulusToriV4ReturnTailClosedFullSupportTrellisGeometryRawEdgeBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_returnTailClosedFullSupportTrellis_blocks
    ⟨hBlocks.1,
      oddSuccessorSmallModulusBaseTailGoal_of_baseTailGeometryRawEdgeColoring
        hBlocks.2⟩

theorem oddSuccessorClosureGoal_of_v4_returnTailTriangular_blocks
    (hBlocks : OddModulusToriV4ReturnTailTriangularBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailTriangular_blocks
      hBlocks.1)
    hBlocks.2

theorem oddSuccessorClosureGoal_of_v4_returnTailTriangularTrellis_blocks
    (hBlocks : OddModulusToriV4ReturnTailTriangularTrellisBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailTriangularTrellis_blocks
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

theorem oddSuccessorClosureGoal_of_v4_returnTailOrbitTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailOrbitTrellis
      hQge2Trellis hOrbit)
    hSmall

theorem oddSuccessorClosureGoal_of_v4_returnTailOrbitAdd
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_returnTailOrbit hQge2Proper hOrbit
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmall)

theorem oddSuccessorClosureGoal_of_v4_returnTailOrbitTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_returnTailOrbitTrellis
    hQge2Trellis hOrbit
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmall)

theorem oddSuccessorClosureGoal_of_v4_returnTailTriangular
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hTri : PrefixCountFirstHitReturnTailTriangularGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailTriangular
      hQge2Proper hTri hUnit)
    hSmall

theorem oddSuccessorClosureGoal_of_v4_returnTailTriangularTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hTri : PrefixCountFirstHitReturnTailTriangularGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailTriangularTrellis
      hQge2Trellis hTri hUnit)
    hSmall

theorem oddSuccessorClosureGoal_of_v4_returnTailTriangularTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hTri : PrefixCountFirstHitReturnTailTriangularGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_returnTailTriangularTrellis
    hQge2Trellis hTri hUnit
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmall)

theorem oddSuccessorClosureGoal_of_v4_returnTailIncrementTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hInc : PrefixCountFirstHitReturnTailIncrementDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_returnTailTriangularTrellis
    hQge2Trellis
    (prefixCountFirstHitReturnTailTriangularGoal_of_incrementDependsOnTake
      hInc)
    hUnit hSmall

theorem oddSuccessorClosureGoal_of_v4_returnTailIncrementTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hInc : PrefixCountFirstHitReturnTailIncrementDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_returnTailIncrementTrellis
    hQge2Trellis hInc hUnit
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmall)

theorem oddSuccessorClosureGoal_of_v4_returnTailFiberIncrementTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hFiber : PrefixCountFirstHitReturnFiberIncrementDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_returnTailIncrementTrellis
    hQge2Trellis
    (prefixCountFirstHitReturnTailIncrementDependsOnTakeGoal_of_fiber
      hFiber)
    hUnit hSmall

theorem oddSuccessorClosureGoal_of_v4_returnTailFiberIncrementTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hFiber : PrefixCountFirstHitReturnFiberIncrementDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_returnTailFiberIncrementTrellis
    hQge2Trellis hFiber hUnit
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmall)

theorem oddSuccessorClosureGoal_of_v4_returnTailHitConditionTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hHit : PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_returnTailFiberIncrementTrellis
    hQge2Trellis
    (prefixCountFirstHitReturnFiberIncrementDependsOnTakeGoal_of_hitCondition
      hHit)
    hUnit hSmall

theorem oddSuccessorClosureGoal_of_v4_returnTailHitConditionTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hHit : PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_returnTailHitConditionTrellis
    hQge2Trellis hHit hUnit
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmall)

theorem oddSuccessorClosureGoal_of_v4_returnTailUnitTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_returnTailHitConditionTrellis
    hQge2Trellis
    prefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal
    hUnit hSmall

theorem oddSuccessorClosureGoal_of_v4_returnTailUnitTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_returnTailUnitTrellis
    hQge2Trellis hUnit
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmall)

theorem oddSuccessorClosureGoal_of_v4_returnTailCocycleSumTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hSum : PrefixCountFirstHitReturnTailCocycleSumGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_returnTailUnitTrellis
    hQge2Trellis
    (prefixCountFirstHitReturnTailCocycleUnitGoal_of_sum hSum)
    hSmall

theorem oddSuccessorClosureGoal_of_v4_returnTailCocycleSumTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hSum : PrefixCountFirstHitReturnTailCocycleSumGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_returnTailCocycleSumTrellis
    hQge2Trellis hSum
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmall)

theorem oddSuccessorClosureGoal_of_v4_returnTailClosedTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_returnTailUnitTrellis
    hQge2Trellis
    prefixCountFirstHitReturnTailCocycleUnitGoal
    hSmall

theorem oddSuccessorClosureGoal_of_v4_returnTailClosedTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_returnTailClosedTrellis
    hQge2Trellis
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

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailOrbitTrellis_blocks
    (hBlocks : OddModulusToriV4ReturnTailOrbitTrellisBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_and_successor_small
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailOrbitTrellis_blocks
      hBlocks.1)
    hBlocks.2
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailClosedTrellis_blocks
    (hBlocks : OddModulusToriV4ReturnTailClosedTrellisBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_and_successor_small
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailClosedTrellis_blocks
      hBlocks.1)
    hBlocks.2
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailClosedFullSupportTrellis_blocks
    (hBlocks : OddModulusToriV4ReturnTailClosedFullSupportTrellisBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailClosedTrellis_blocks
    ⟨oddCoreHighModulusReturnTailClosedTrellisBlocksGoal_of_fullSupport
        hBlocks.1,
      hBlocks.2⟩
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailClosedFullSupportTrellisGeometryEdge_blocks
    (hBlocks :
      OddModulusToriV4ReturnTailClosedFullSupportTrellisGeometryEdgeBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailClosedFullSupportTrellis_blocks
    ⟨hBlocks.1,
      oddSuccessorSmallModulusBaseTailGoal_of_baseTailGeometryExactEdgeColoring
        hBlocks.2⟩
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailClosedFullSupportTrellisGeometryRawEdge_blocks
    (hBlocks :
      OddModulusToriV4ReturnTailClosedFullSupportTrellisGeometryRawEdgeBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailClosedFullSupportTrellis_blocks
    ⟨hBlocks.1,
      oddSuccessorSmallModulusBaseTailGoal_of_baseTailGeometryRawEdgeColoring
        hBlocks.2⟩
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailOrbitTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailOrbitTrellis_blocks
    ⟨⟨hQge2Trellis, hOrbit⟩, hSmall⟩
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

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailOrbitTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailOrbitTrellis
    hQge2Trellis hOrbit
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmall)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailOrbitTrellisAdd_blocks
    (hBlocks : OddModulusToriV4ReturnTailOrbitTrellisAddBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailOrbitTrellis_blocks
    ⟨hBlocks.1,
      oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hBlocks.2⟩
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailTriangular_blocks
    (hBlocks : OddModulusToriV4ReturnTailTriangularBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_and_successor_small
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailTriangular_blocks
      hBlocks.1)
    hBlocks.2
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailTriangular
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hTri : PrefixCountFirstHitReturnTailTriangularGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailTriangular_blocks
    ⟨⟨hQge2Proper, ⟨hTri, hUnit⟩⟩, hSmall⟩
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailTriangularTrellis_blocks
    (hBlocks : OddModulusToriV4ReturnTailTriangularTrellisBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_and_successor_small
    (oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailTriangularTrellis_blocks
      hBlocks.1)
    hBlocks.2
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailTriangularTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hTri : PrefixCountFirstHitReturnTailTriangularGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailTriangularTrellis_blocks
    ⟨⟨hQge2Trellis, ⟨hTri, hUnit⟩⟩, hSmall⟩
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailTriangularTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hTri : PrefixCountFirstHitReturnTailTriangularGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailTriangularTrellis
    hQge2Trellis hTri hUnit
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmall)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailTriangularTrellisAdd_blocks
    (hBlocks : OddModulusToriV4ReturnTailTriangularTrellisAddBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailTriangularTrellis_blocks
    ⟨hBlocks.1,
      oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hBlocks.2⟩
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailIncrementTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hInc : PrefixCountFirstHitReturnTailIncrementDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailTriangularTrellis
    hQge2Trellis
    (prefixCountFirstHitReturnTailTriangularGoal_of_incrementDependsOnTake
      hInc)
    hUnit hSmall hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailIncrementTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hInc : PrefixCountFirstHitReturnTailIncrementDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailIncrementTrellis
    hQge2Trellis hInc hUnit
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmall)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailFiberIncrementTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hFiber : PrefixCountFirstHitReturnFiberIncrementDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailIncrementTrellis
    hQge2Trellis
    (prefixCountFirstHitReturnTailIncrementDependsOnTakeGoal_of_fiber
      hFiber)
    hUnit hSmall hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailFiberIncrementTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hFiber : PrefixCountFirstHitReturnFiberIncrementDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailFiberIncrementTrellis
    hQge2Trellis hFiber hUnit
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmall)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailHitConditionTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hHit : PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailFiberIncrementTrellis
    hQge2Trellis
    (prefixCountFirstHitReturnFiberIncrementDependsOnTakeGoal_of_hitCondition
      hHit)
    hUnit hSmall hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailHitConditionTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hHit : PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailHitConditionTrellis
    hQge2Trellis hHit hUnit
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmall)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailUnitTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailHitConditionTrellis
    hQge2Trellis
    prefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal
    hUnit hSmall hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailUnitTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailUnitTrellis
    hQge2Trellis hUnit
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmall)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailCocycleSumTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hSum : PrefixCountFirstHitReturnTailCocycleSumGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailUnitTrellis
    hQge2Trellis
    (prefixCountFirstHitReturnTailCocycleUnitGoal_of_sum hSum)
    hSmall hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailCocycleSumTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hSum : PrefixCountFirstHitReturnTailCocycleSumGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailCocycleSumTrellis
    hQge2Trellis hSum
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmall)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailClosedTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailUnitTrellis
    hQge2Trellis
    prefixCountFirstHitReturnTailCocycleUnitGoal
    hSmall hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailClosedFullSupportTrellis
    (hFull : PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailClosedTrellis
    (PrefixCount.ordinaryQge2SignedTrellisHoffmanGoal_of_fullSupport
      hFull hLift)
    hSmall hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailClosedFullSupportTrellisGeometryEdge
    (hFull : PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal)
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hEdge : ActiveHall.FiniteHoffman.ExactEdgeColoringGoal.{0, 0})
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailClosedFullSupportTrellis
    hFull hLift
    (oddSuccessorSmallModulusBaseTailGoal_of_baseTailGeometryFromExactEdgeColoring
      hGeom hEdge)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailClosedFullSupportTrellisGeometryRawEdge
    (hFull : PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal)
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hRaw : ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal.{0, 0})
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailClosedFullSupportTrellisGeometryEdge
    hFull hLift hGeom
    (ActiveHall.FiniteHoffman.exactEdgeColoringGoal_of_raw hRaw)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailClosedTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailClosedTrellis
    hQge2Trellis
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmall)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_returnTailClosedFullSupportTrellisAdd
    (hFull : PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailClosedFullSupportTrellis
    hFull hLift
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

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailOrbitTrellis_blocks
    (hBlocks : OddModulusToriV4ReturnTailOrbitTrellisBlocksGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailOrbitTrellis_blocks
    hBlocks hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedTrellis_blocks
    (hBlocks : OddModulusToriV4ReturnTailClosedTrellisBlocksGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailClosedTrellis_blocks
    hBlocks hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedFullSupportTrellis_blocks
    (hBlocks : OddModulusToriV4ReturnTailClosedFullSupportTrellisBlocksGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailClosedFullSupportTrellis_blocks
    hBlocks hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedFullSupportTrellisGeometryEdge_blocks
    (hBlocks :
      OddModulusToriV4ReturnTailClosedFullSupportTrellisGeometryEdgeBlocksGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact
    odd_modulus_tori_all_dimensions_of_v4_returnTailClosedFullSupportTrellisGeometryEdge_blocks
      hBlocks hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedFullSupportTrellisGeometryRawEdge_blocks
    (hBlocks :
      OddModulusToriV4ReturnTailClosedFullSupportTrellisGeometryRawEdgeBlocksGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact
    odd_modulus_tori_all_dimensions_of_v4_returnTailClosedFullSupportTrellisGeometryRawEdge_blocks
      hBlocks hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailOrbitTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailOrbitTrellis
    hQge2Trellis hOrbit hSmall hd2 hmodd hm3

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

theorem odd_modulus_tori_all_dimensions_of_v4_seedProper_geometry_rawEdge
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hRaw : ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal.{0, 0})
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_returnTailOrbit
    hQge2Proper
    prefixCountFirstHitReturnTailMonodromyOrbitGoal
    (oddSuccessorSmallModulusBaseTailGoal_of_baseTailGeometryFromRawEdgeColoring
      hGeom hRaw)
    hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_seedProper_geometry_rawEdge
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hRaw : ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal.{0, 0}) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_seedProper_geometry_rawEdge
    hQge2Proper hGeom hRaw hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_seedProper_geometry_deWerra
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hDW : ActiveHall.FiniteHoffman.CompatibleDeWerraGoal.{0, 0})
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_seedProper_geometry_rawEdge
    hQge2Proper hGeom
    (ActiveHall.FiniteHoffman.rawExactEdgeColoringGoal_of_compatibleDeWerra hDW)
    hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_seedProper_geometry_deWerra
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hDW : ActiveHall.FiniteHoffman.CompatibleDeWerraGoal.{0, 0}) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_seedProper_geometry_deWerra
    hQge2Proper hGeom hDW hd2 hmodd hm3

def OddModulusToriV4CompletionCoreRawMatrixGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal ∧
  ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0, 0}

def OddModulusToriV4CompletionCoreCompatibleMatrixGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal ∧
  ActiveHall.FiniteHoffman.CompatibleZeroOneMatrixGoal.{0, 0}

def OddModulusToriV4CompletionCoreHallGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal ∧
  ActiveHall.HallRealizationGoal.{0, 0}

theorem odd_modulus_tori_all_dimensions_of_v4_seedProper_core_rawMatrix
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hCore : OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal)
    (hMat : ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0, 0})
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_seedProper_geometry_rawEdge
    hQge2Proper
    (oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_core hCore)
    (ActiveHall.FiniteHoffman.rawExactEdgeColoringGoal_of_rawMatrix hMat)
    hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_seedProper_core_rawMatrix
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hCore : OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal)
    (hMat : ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0, 0}) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_seedProper_core_rawMatrix
    hQge2Proper hCore hMat hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_completionCoreRawMatrix
    (hCore : OddModulusToriV4CompletionCoreRawMatrixGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v4_seedProper_core_rawMatrix
    hCore.1 hCore.2.1 hCore.2.2

theorem odd_modulus_tori_all_dimensions_of_v4_seedProper_core_compatibleMatrix
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hCore : OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal)
    (hMat : ActiveHall.FiniteHoffman.CompatibleZeroOneMatrixGoal.{0, 0})
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_seedProper_geometry_rawEdge
    hQge2Proper
    (oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_core hCore)
    (ActiveHall.FiniteHoffman.rawExactEdgeColoringGoal_of_matrix hMat)
    hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_seedProper_core_compatibleMatrix
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hCore : OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal)
    (hMat : ActiveHall.FiniteHoffman.CompatibleZeroOneMatrixGoal.{0, 0}) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_seedProper_core_compatibleMatrix
    hQge2Proper hCore hMat hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_completionCoreCompatibleMatrix
    (hCore : OddModulusToriV4CompletionCoreCompatibleMatrixGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v4_seedProper_core_compatibleMatrix
    hCore.1 hCore.2.1 hCore.2.2

theorem odd_modulus_tori_all_dimensions_of_v4_seedProper_core_hall
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hCore : OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal)
    (hHall : ActiveHall.HallRealizationGoal.{0, 0})
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_seedProper_geometry_rawEdge
    hQge2Proper
    (oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_core hCore)
    (ActiveHall.FiniteHoffman.rawExactEdgeColoringGoal_of_hallRealizationGoal
      hHall)
    hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_seedProper_core_hall
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hCore : OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal)
    (hHall : ActiveHall.HallRealizationGoal.{0, 0}) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_seedProper_core_hall
    hQge2Proper hCore hHall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_completionCoreHall
    (hCore : OddModulusToriV4CompletionCoreHallGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v4_seedProper_core_hall
    hCore.1 hCore.2.1 hCore.2.2

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailOrbitTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailOrbitTrellisAdd
    hQge2Trellis hOrbit hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailOrbitTrellisAdd_blocks
    (hBlocks : OddModulusToriV4ReturnTailOrbitTrellisAddBlocksGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailOrbitTrellisAdd_blocks
    hBlocks hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailTriangular_blocks
    (hBlocks : OddModulusToriV4ReturnTailTriangularBlocksGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailTriangular_blocks
    hBlocks hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailTriangular
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hTri : PrefixCountFirstHitReturnTailTriangularGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailTriangular
    hQge2Proper hTri hUnit hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailTriangularTrellis_blocks
    (hBlocks : OddModulusToriV4ReturnTailTriangularTrellisBlocksGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailTriangularTrellis_blocks
    hBlocks hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailTriangularTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hTri : PrefixCountFirstHitReturnTailTriangularGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailTriangularTrellis
    hQge2Trellis hTri hUnit hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailTriangularTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hTri : PrefixCountFirstHitReturnTailTriangularGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailTriangularTrellisAdd
    hQge2Trellis hTri hUnit hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailTriangularTrellisAdd_blocks
    (hBlocks : OddModulusToriV4ReturnTailTriangularTrellisAddBlocksGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailTriangularTrellisAdd_blocks
    hBlocks hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailIncrementTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hInc : PrefixCountFirstHitReturnTailIncrementDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailIncrementTrellis
    hQge2Trellis hInc hUnit hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailIncrementTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hInc : PrefixCountFirstHitReturnTailIncrementDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailIncrementTrellisAdd
    hQge2Trellis hInc hUnit hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailFiberIncrementTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hFiber : PrefixCountFirstHitReturnFiberIncrementDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailFiberIncrementTrellis
    hQge2Trellis hFiber hUnit hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailFiberIncrementTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hFiber : PrefixCountFirstHitReturnFiberIncrementDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailFiberIncrementTrellisAdd
    hQge2Trellis hFiber hUnit hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailHitConditionTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hHit : PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailHitConditionTrellis
    hQge2Trellis hHit hUnit hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailHitConditionTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hHit : PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailHitConditionTrellisAdd
    hQge2Trellis hHit hUnit hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailUnitTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailUnitTrellis
    hQge2Trellis hUnit hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailUnitTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailUnitTrellisAdd
    hQge2Trellis hUnit hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailCocycleSumTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hSum : PrefixCountFirstHitReturnTailCocycleSumGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailCocycleSumTrellis
    hQge2Trellis hSum hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailCocycleSumTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hSum : PrefixCountFirstHitReturnTailCocycleSumGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailCocycleSumTrellisAdd
    hQge2Trellis hSum hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailClosedTrellis
    hQge2Trellis hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedFullSupportTrellis
    (hFull : PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailClosedFullSupportTrellis
    hFull hLift hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedFullSupportTrellisGeometryEdge
    (hFull : PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal)
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hEdge : ActiveHall.FiniteHoffman.ExactEdgeColoringGoal.{0, 0}) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact
    odd_modulus_tori_all_dimensions_of_v4_returnTailClosedFullSupportTrellisGeometryEdge
      hFull hLift hGeom hEdge hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedFullSupportTrellisGeometryRawEdge
    (hFull : PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal)
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hRaw : ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal.{0, 0}) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact
    odd_modulus_tori_all_dimensions_of_v4_returnTailClosedFullSupportTrellisGeometryRawEdge
      hFull hLift hGeom hRaw hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailClosedTrellisAdd
    hQge2Trellis hSmall hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedFullSupportTrellisAdd
    (hFull : PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact odd_modulus_tori_all_dimensions_of_v4_returnTailClosedFullSupportTrellisAdd
    hFull hLift hSmall hd2 hmodd hm3

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
