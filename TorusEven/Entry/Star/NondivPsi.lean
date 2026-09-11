-- STATUS: main-path
import TorusEven.Entry.Star.NondivInner

namespace TorusEven.Entry.Star.Nondivisible

open Surgery

def psiIndex (k i : ℕ) : ℕ :=
  if i < k - 2 then i + k + 1 else
  if i = k - 2 then k - 1 else
  if i < 2 * k - 3 then i + 2 - k else
  if i = 2 * k - 3 then k else 0

variable (k : ℕ) (hk : 4 ≤ k)
include hk

theorem psiIndex_lt (i : Fin (2 * k - 1)) : psiIndex k i.val < 2 * k - 1 := by
  unfold psiIndex
  split_ifs <;> have := i.isLt <;> omega

noncomputable def psi : Equiv.Perm (Fin (2 * k - 1)) := Equiv.ofBijective
  (fun i => ⟨psiIndex k i.val, psiIndex_lt k hk i⟩) (by
    have hi : Function.Injective (fun i : Fin (2 * k - 1) =>
        (⟨psiIndex k i.val, psiIndex_lt k hk i⟩ : Fin (2 * k - 1))) := by
      intro i j h
      apply Fin.ext
      have he := congrArg Fin.val h
      change psiIndex k i.val = psiIndex k j.val at he
      unfold psiIndex at he
      split_ifs at he <;> have := i.isLt <;> have := j.isLt <;> omega
    exact ⟨hi, Finite.surjective_of_injective hi⟩)

theorem psi_val (i : Fin (2 * k - 1)) : (psi k hk i).val = psiIndex k i.val := rfl

def lowerEmbedding (i : Fin (k - 1)) : Fin (2 * k - 1) := ⟨i.val, by have := i.isLt; omega⟩

theorem lower_step (i : Fin (k - 1)) :
    lowerEmbedding k hk (chi k hk i) ∈ orbitSet (psi k hk) (lowerEmbedding k hk i) := by
  have hi := i.isLt
  by_cases he : i.val = k - 4
  · refine ⟨3, ?_⟩
    dsimp only
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    apply Fin.ext
    change psiIndex k (psiIndex k (psiIndex k i.val)) = chiIndex k i.val
    simp (disch := omega) only [psiIndex, chiIndex, if_pos, if_neg]
    omega
  · refine ⟨2, ?_⟩
    dsimp only
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    apply Fin.ext
    change psiIndex k (psiIndex k i.val) = chiIndex k i.val
    by_cases hl : i.val < k - 4 <;> by_cases hm : i.val = k - 3 <;> try omega
    all_goals simp (disch := omega) only [psiIndex, chiIndex, if_pos, if_neg]
    all_goals omega

theorem psi_meets_lower (i : Fin (2 * k - 1)) :
    ∃ j, lowerEmbedding k hk j ∈ orbitSet (psi k hk) i := by
  have hi := i.isLt
  by_cases hl : i.val < k - 1
  · exact ⟨⟨i.val, hl⟩, 0, rfl⟩
  by_cases hp : i.val = 2 * k - 3
  · refine ⟨⟨2, by omega⟩, 2, ?_⟩
    dsimp only
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    apply Fin.ext
    change psiIndex k (psiIndex k i.val) = 2
    unfold psiIndex
    split_ifs <;> first | contradiction | omega
  · have hv : (psi k hk i).val < k - 1 := by
      rw [psi_val]
      unfold psiIndex
      split_ifs <;> omega
    exact ⟨⟨(psi k hk i).val, hv⟩, 1, rfl⟩

theorem psi_hamilton (hd : ¬ 3 ∣ k) : Shared.IsSingleCycleMap (psi k hk) :=
  singleCycle_of_induced_orbits (psi k hk) (lowerEmbedding k hk) (chi k hk)
    (chi_hamilton k hk hd) (lower_step k hk) (psi_meets_lower k hk)

end TorusEven.Entry.Star.Nondivisible
