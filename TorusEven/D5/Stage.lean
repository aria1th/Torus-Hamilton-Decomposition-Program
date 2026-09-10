-- STATUS: main-path (one chronological stage: layers → return orbits)
import TorusEven.D5.Layers
import TorusEven.D5.Chronological
import TorusEven.D5.Certificates

/-!
# One chronological stage

Given layers `L` whose full return has orbits equal to the cosets of `H`, whose prefix up to
height `t` is a translation modulo `H`, and a complement `W` with `e ∈ W`, replacing the
layer `L t` by `L t ∘ J` (`J` adding `e` on the affine coset `z + W`) yields a return whose
orbits are the cosets of `H ⊔ ⟨e⟩`.  This packages `Layers.pre_change` with the
chronological transversal lemma.  Also: translations, whose orbits are the cosets of the
cyclic subgroup they generate.
-/

namespace TorusEven
namespace Stage

open Chronological

variable {m : ℕ} [NeZero m]

abbrev V (m : ℕ) := Fin 4 → ZMod m

theorem orbitSet_translation (v : V m) (x : V m) :
    orbitSet (fun y => y + v) x = coset (AddSubgroup.zmultiples v) x := by
  have hiter : ∀ n : ℕ, (fun y : V m => y + v)^[n] x = x + n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih, succ_nsmul, add_assoc]
  have h := sup_zmultiples_coset_eq (⊥ : AddSubgroup (V m)) v x
  rw [bot_sup_eq] at h
  rw [h]
  ext y
  simp only [Set.mem_iUnion, coset_def', AddSubgroup.mem_bot, sub_eq_zero]
  constructor
  · rintro ⟨n, rfl⟩
    dsimp only
    rw [hiter]
    obtain ⟨p, hp, hper⟩ := Function.mem_periodicPts.1
      ((add_left_injective v).mem_periodicPts x)
    -- `x + n • v = x + (n + p * k) • v`; choose `k` so that the exponent is ≥ 1
    refine ⟨n + p - 1, ?_⟩
    have hpv : x + p • v = x := by
      have := hper.eq
      rwa [hiter] at this
    have hpv' : p • v = 0 := by
      have := congrArg (· - x) hpv
      simpa using this
    have : n + p - 1 + 1 = n + p := by omega
    rw [this, add_nsmul, hpv', add_zero]
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, by dsimp only; rw [hiter, hk]⟩

/-- Prefix of translation-plus-correction layers is a translation modulo `H`. -/
theorem prefix_mem (L : ℕ → V m → V m) (nu : ℕ → V m) (H : AddSubgroup (V m))
    (hL : ∀ s x, L s x - x - nu s ∈ H) :
    ∀ t x, Layers.pre L t x - x - (∑ s ∈ Finset.range t, nu s) ∈ H := by
  intro t
  induction t with
  | zero => intro x; simp
  | succ t ih =>
      intro x
      rw [Layers.pre_succ, Function.comp, Finset.sum_range_succ]
      have h1 := hL t (Layers.pre L t x)
      have h2 := ih x
      have : L t (Layers.pre L t x) - x - (∑ s ∈ Finset.range t, nu s + nu t) =
          (L t (Layers.pre L t x) - Layers.pre L t x - nu t) +
            (Layers.pre L t x - x - ∑ s ∈ Finset.range t, nu s) := by abel
      rw [this]
      exact H.add_mem h1 h2

/-- The chronological stage. -/
theorem step (L L' : ℕ → V m → V m) (hL : ∀ s, Function.Bijective (L s))
    (t : ℕ) (ht : t < m)
    (H W : AddSubgroup (V m)) [DecidablePred (· ∈ W)] (hHW : IsCompl H W)
    (hS : ∀ x, orbitSet (Layers.pre L m) x = coset H x)
    (b : V m) (hP : ∀ x, Layers.pre L t x - x - b ∈ H)
    (z e : V m) (he : e ∈ W)
    (hL' : ∀ s, s ≠ t → L' s = L s) (hLt : L' t = L t ∘ piecewiseAdd W z e) :
    ∀ x, orbitSet (Layers.pre L' m) x = coset (H ⊔ AddSubgroup.zmultiples e) x := by
  let P : Equiv.Perm (V m) := Equiv.ofBijective _ (Layers.pre_bijective L hL t)
  let S : Equiv.Perm (V m) := Equiv.ofBijective _ (Layers.pre_bijective L hL m)
  have hPeq : ⇑P = Layers.pre L t := rfl
  have hSeq : ⇑S = Layers.pre L m := rfl
  have hchange := Layers.pre_change L L' t m ht (piecewiseAdd W z e) (fun s hs _ => hL' s hs) hLt P hPeq
  intro x
  have hmain := chronological_transversal H W hHW S (by simpa [hSeq] using hS) P b
    (by simpa [hPeq] using hP) e he (addOrderOf e) rfl z x
  simp only at hmain
  rw [hchange]
  convert hmain using 2

end Stage
end TorusEven
