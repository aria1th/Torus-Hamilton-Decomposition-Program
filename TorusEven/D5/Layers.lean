-- STATUS: main-path (fold algebra: changing one layer changes the return by P⁻¹ J P)
import Mathlib
import Shared.RootFlat

/-!
# Layer folds

`pre L n = L (n-1) ∘ ⋯ ∘ L 0`.  If `L'` agrees with `L` except that `L' t = L t ∘ J`, then
`pre L' n = pre L n ∘ (P⁻¹ ∘ J ∘ P)` with `P = pre L t`
(manuscript identity `eq:chronological-identity`).
-/

namespace TorusEven
namespace Layers

variable {α : Type*}

/-- Composite of the layers `0, …, n-1`, latest applied last. -/
def pre (L : ℕ → α → α) : ℕ → α → α
  | 0 => id
  | n + 1 => L n ∘ pre L n

@[simp] theorem pre_zero (L : ℕ → α → α) : pre L 0 = id := rfl

@[simp] theorem pre_succ (L : ℕ → α → α) (n : ℕ) : pre L (n + 1) = L n ∘ pre L n := rfl

theorem pre_eq_foldl (L : ℕ → α → α) (n : ℕ) (x : α) :
    pre L n x = (List.range n).foldl (fun y t => L t y) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, pre_succ]
      simp [ih]

theorem pre_bijective (L : ℕ → α → α) (hL : ∀ t, Function.Bijective (L t)) (n : ℕ) :
    Function.Bijective (pre L n) := by
  induction n with
  | zero => exact Function.bijective_id
  | succ n ih => exact (hL n).comp ih

/-- Composite of the layers `k, …, n-1`. -/
def suf (L : ℕ → α → α) (k : ℕ) : ℕ → α → α
  | 0 => id
  | n + 1 => if k ≤ n then L n ∘ suf L k n else id

theorem pre_eq_suf_comp_pre (L : ℕ → α → α) (k : ℕ) :
    ∀ n, k ≤ n → pre L n = suf L k n ∘ pre L k := by
  intro n
  induction n with
  | zero =>
      intro hk
      have : k = 0 := by omega
      subst this
      rfl
  | succ n ih =>
      intro hk
      rcases Nat.lt_or_ge n k with hlt | hge
      · have : k = n + 1 := by omega
        subst this
        simp [suf]
      · simp only [pre_succ, suf, hge, if_true]
        rw [ih hge]
        rfl

theorem pre_congr (L L' : ℕ → α → α) (n : ℕ) (h : ∀ s, s < n → L' s = L s) :
    pre L' n = pre L n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pre_succ]
      rw [h n (by omega), ih (fun s hs => h s (by omega))]

theorem suf_congr (L L' : ℕ → α → α) (k n : ℕ) (h : ∀ s, k ≤ s → s < n → L' s = L s) :
    suf L' k n = suf L k n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [suf]
      split_ifs with hk
      · rw [h n hk (by omega), ih (fun s hs hs' => h s hs (by omega))]
      · rfl

/-- The chronological identity. -/
theorem pre_change (L L' : ℕ → α → α) (t n : ℕ) (ht : t < n) (J : α → α)
    (hL' : ∀ s, s ≠ t → L' s = L s) (hLt : L' t = L t ∘ J) (P : α ≃ α) (hP : ⇑P = pre L t) :
    pre L' n = pre L n ∘ (P.symm ∘ J ∘ P) := by
  have hpre : pre L' t = pre L t := pre_congr L L' t (fun s hs => hL' s (by omega))
  have hsuf : suf L' (t + 1) n = suf L (t + 1) n :=
    suf_congr L L' (t + 1) n (fun s hs _ => hL' s (by omega))
  rw [pre_eq_suf_comp_pre L' (t + 1) n ht, pre_eq_suf_comp_pre L (t + 1) n ht, hsuf]
  funext x
  simp only [Function.comp, pre_succ, hLt, hpre]
  congr 2
  rw [← hP, Equiv.apply_symm_apply]

end Layers
end TorusEven
