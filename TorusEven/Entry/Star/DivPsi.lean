-- STATUS: main-path
import TorusEven.Entry.Star.InnerReturn
import TorusEven.Entry.Star.Induced

namespace TorusEven.Entry.Star.Divisible

open Surgery

variable (q : ℕ) (hq : 2 ≤ q)

def betaIndex (i : ℕ) : ℕ :=
  if i + (2 * q + 1) < 6 * q - 1 then i + (2 * q + 1)
  else i + (2 * q + 1) - (6 * q - 1)

def psiIndex (i : ℕ) : ℕ :=
  if betaIndex q i < 2 * q + 1 then InnerReturn.thetaIndex q (betaIndex q i)
  else betaIndex q i

include hq

theorem betaIndex_lt (i : Fin (6 * q - 1)) : betaIndex q i.val < 6 * q - 1 := by
  unfold betaIndex
  split_ifs <;> have := i.isLt <;> omega

noncomputable def beta : Equiv.Perm (Fin (6 * q - 1)) := Equiv.ofBijective
  (fun i => ⟨betaIndex q i.val, betaIndex_lt q hq i⟩) (by
    have hi : Function.Injective (fun i : Fin (6 * q - 1) =>
        (⟨betaIndex q i.val, betaIndex_lt q hq i⟩ : Fin (6 * q - 1))) := by
      intro i j h
      apply Fin.ext
      have he := congrArg Fin.val h
      change betaIndex q i.val = betaIndex q j.val at he
      unfold betaIndex at he
      split_ifs at he <;> have := i.isLt <;> have := j.isLt <;> omega
    exact ⟨hi, Finite.surjective_of_injective hi⟩)

def innerEmbedding : Fin (2 * q + 1) ↪ Fin (6 * q - 1) where
  toFun i := ⟨i.val, by have := i.isLt; omega⟩
  inj' _ _ h := Fin.ext (congrArg (fun i : Fin (6 * q - 1) => i.val) h)

noncomputable def psi : Equiv.Perm (Fin (6 * q - 1)) :=
  (beta q hq).trans ((InnerReturn.thetaPerm q hq).viaEmbedding (innerEmbedding q hq))

theorem psi_val (i : Fin (6 * q - 1)) : (psi q hq i).val = psiIndex q i.val := by
  by_cases hi : betaIndex q i.val < 2 * q + 1
  · have he : beta q hq i = innerEmbedding q hq ⟨betaIndex q i.val, hi⟩ := rfl
    rw [psi, Equiv.trans_apply, he, Equiv.Perm.viaEmbedding_apply]
    simp only [innerEmbedding, Function.Embedding.coeFn_mk, InnerReturn.thetaPerm,
      Equiv.ofBijective_apply, InnerReturn.theta, psiIndex, if_pos hi]
  · have he : beta q hq i ∉ Set.range (innerEmbedding q hq) := by
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      change j.val = betaIndex q i.val at hv
      exact hi (hv ▸ j.isLt)
    rw [psi, Equiv.trans_apply, Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ he]
    simp only [beta, Equiv.ofBijective_apply, psiIndex, if_neg hi]

theorem psi_inner_first (i : Fin (2 * q + 1)) :
    (psi q hq (innerEmbedding q hq i)).val = i.val + (2 * q + 1) := by
  rw [psi_val]
  change psiIndex q i.val = _
  have hi := i.isLt
  simp only [psiIndex, betaIndex, if_pos (by omega : i.val + (2 * q + 1) < 6 * q - 1),
    if_neg (by omega : ¬ i.val + (2 * q + 1) < 2 * q + 1)]

theorem psi_inner_return (i : Fin (2 * q + 1)) :
    ∃ n, (psi q hq)^[n] (innerEmbedding q hq i) =
      innerEmbedding q hq (InnerReturn.step q hq i) := by
  have hi := i.isLt
  by_cases hl : i.val + 4 < 2 * q + 1
  · have h2 : ((psi q hq)^[2] (innerEmbedding q hq i)).val = i.val + 2 * (2 * q + 1) := by
      rw [Function.iterate_succ_apply', Function.iterate_one, psi_val, psi_inner_first]
      simp only [psiIndex, betaIndex,
        if_pos (by omega : i.val + (2 * q + 1) + (2 * q + 1) < 6 * q - 1),
        if_neg (by omega : ¬ i.val + (2 * q + 1) + (2 * q + 1) < 2 * q + 1)]
      omega
    refine ⟨3, Fin.ext ?_⟩
    rw [Function.iterate_succ_apply', psi_val, h2]
    change psiIndex q (i.val + 2 * (2 * q + 1)) =
      InnerReturn.thetaIndex q (InnerReturn.shiftIndex q i.val)
    simp only [psiIndex, betaIndex,
      if_neg (by omega : ¬ i.val + 2 * (2 * q + 1) + (2 * q + 1) < 6 * q - 1),
      if_pos (by omega : i.val + 2 * (2 * q + 1) + (2 * q + 1) - (6 * q - 1) < 2 * q + 1),
      InnerReturn.shiftIndex, if_pos hl]
    congr 1; omega
  · refine ⟨2, Fin.ext ?_⟩
    rw [Function.iterate_succ_apply', Function.iterate_one, psi_val, psi_inner_first]
    change psiIndex q (i.val + (2 * q + 1)) =
      InnerReturn.thetaIndex q (InnerReturn.shiftIndex q i.val)
    simp only [psiIndex, betaIndex,
      if_neg (by omega : ¬ i.val + (2 * q + 1) + (2 * q + 1) < 6 * q - 1),
      if_pos (by omega : i.val + (2 * q + 1) + (2 * q + 1) - (6 * q - 1) < 2 * q + 1),
      InnerReturn.shiftIndex, if_neg hl]
    congr 1; omega

theorem psi_meets_inner (i : Fin (6 * q - 1)) :
    ∃ j, innerEmbedding q hq j ∈ orbitSet (psi q hq) i := by
  have hi := i.isLt
  by_cases hl : i.val < 2 * q + 1
  · exact ⟨⟨i.val, hl⟩, 0, rfl⟩
  · by_cases hb : i.val + (2 * q + 1) < 6 * q - 1
    · have h1 : (psi q hq i).val = i.val + (2 * q + 1) := by
        rw [psi_val]
        simp only [psiIndex, betaIndex, if_pos hb, if_neg (by omega :
          ¬ i.val + (2 * q + 1) < 2 * q + 1)]
      have hj : i.val + (2 * q + 1) + (2 * q + 1) - (6 * q - 1) < 2 * q + 1 := by omega
      let j : Fin (2 * q + 1) := ⟨_, hj⟩
      refine ⟨InnerReturn.theta q hq j, 2, Fin.ext ?_⟩
      dsimp only
      rw [Function.iterate_succ_apply', Function.iterate_one, psi_val, h1]
      change psiIndex q (i.val + (2 * q + 1)) = InnerReturn.thetaIndex q j.val
      simp only [psiIndex, betaIndex,
        if_neg (by omega : ¬ i.val + (2 * q + 1) + (2 * q + 1) < 6 * q - 1), if_pos hj]
      rfl
    · have hj : i.val + (2 * q + 1) - (6 * q - 1) < 2 * q + 1 := by omega
      let j : Fin (2 * q + 1) := ⟨_, hj⟩
      refine ⟨InnerReturn.theta q hq j, 1, Fin.ext ?_⟩
      dsimp only
      rw [Function.iterate_one, psi_val]
      change psiIndex q i.val = InnerReturn.thetaIndex q j.val
      simp only [psiIndex, betaIndex, if_neg hb, if_pos hj]
      rfl

theorem psi_hamilton : Shared.IsSingleCycleMap (psi q hq) :=
  singleCycle_of_induced_orbits (psi q hq) (innerEmbedding q hq) (InnerReturn.step q hq)
    (InnerReturn.hamilton q hq) (psi_inner_return q hq) (psi_meets_inner q hq)

end TorusEven.Entry.Star.Divisible
