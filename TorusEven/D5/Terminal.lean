-- STATUS: main-path (the terminal surgery: pairs on cosets + a covering orbit ⇒ single cycle)
import TorusEven.D5.FirstReturn
import TorusEven.D5.Chronological

/-!
# The terminal splice (manuscript Theorem `thm:d5large`, second half)

Abstract form: `S` has orbits equal to the cosets of `K`; `U` meets every coset in exactly two
points exchanged by `pair`; `J` is a permutation supported on `U`; if the orbit of some `u ∈ U`
under `pair ∘ J` is all of `U`, then `S ∘ J` is a single cycle.
-/

namespace TorusEven
namespace TerminalSplice

open Function Surgery Chronological

variable {X : Type} [AddCommGroup X] [Fintype X] [DecidableEq X]

theorem single_cycle
    (S : Equiv.Perm X) (K : AddSubgroup X) (hS : ∀ x, Surgery.orbitSet S x = coset K x)
    (U : Set X) [DecidablePred (· ∈ U)]
    (J : X → X) (hJ : Bijective J) (hsupp : ∀ x, x ∉ U → J x = x) (hmaps : ∀ x, x ∈ U → J x ∈ U)
    (hmeet : ∀ x, ∃ w ∈ U, w ∈ coset K x)
    (pair : X → X) (hpair_mem : ∀ w ∈ U, pair w ∈ U) (hpair_ne : ∀ w ∈ U, pair w ≠ w)
    (hpair_coset : ∀ w ∈ U, pair w ∈ coset K w)
    (huniq : ∀ w ∈ U, ∀ y ∈ U, y ∈ coset K w → y = w ∨ y = pair w)
    (u : X) (hu : u ∈ U) (hcover : ∀ w ∈ U, ∃ k, (fun y => pair (J y))^[k] u = w) :
    Shared.IsSingleCycleMap (fun x => S (J x)) := by
  -- the first return on `U` is the pair map
  have hret : ∀ w ∈ U, ret S U w = pair w := by
    intro w hw
    apply ret_eq_of_pair S U hw (hpair_mem w hw) (hpair_ne w hw)
    · rw [hS]; exact hpair_coset w hw
    · intro y hy hyU
      rw [hS] at hy
      exact huniq w hw y hyU hy
  have hafter : ∀ w ∈ U, afterRet S U J w = pair (J w) := by
    intro w hw
    unfold afterRet
    exact hret _ (hmaps w hw)
  have hafter_iter : ∀ k, (afterRet S U J)^[k] u = (fun y => pair (J y))^[k] u := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        apply hafter
        rw [← ih]
        exact afterRet_iterate_mem S U J hmaps hu k
  have horbU : Surgery.orbitSet (afterRet S U J) u = U := by
    ext w
    constructor
    · rintro ⟨k, rfl⟩
      exact afterRet_iterate_mem S U J hmaps hu k
    · intro hw
      obtain ⟨k, hk⟩ := hcover w hw
      exact ⟨k, by dsimp only; rw [hafter_iter, hk]⟩
  have hSJ : Bijective (fun x => S (J x)) := S.bijective.comp hJ
  refine single_cycle_of_orbitSet_univ hSJ u ?_
  have h := orbitSet_comp_eq S U J hsupp hmaps hJ hu
  have hid : (⇑S ∘ J) = fun x => S (J x) := rfl
  rw [hid] at h
  rw [h, horbU]
  -- `⋃_{v ∈ U} seg (J v) = ⋃_{w ∈ U} seg w` since `J` permutes `U`
  have hJU : ∀ w ∈ U, ∃ v ∈ U, J v = w := by
    intro w hw
    obtain ⟨v, hv⟩ := hJ.2 w
    refine ⟨v, ?_, hv⟩
    by_contra hvU
    have := hsupp v hvU
    rw [this] at hv
    exact hvU (hv ▸ hw)
  have hmeet' : ∀ x, ∃ w ∈ U, w ∈ Surgery.orbitSet S x := by
    intro x
    obtain ⟨w, hwU, hw⟩ := hmeet x
    exact ⟨w, hwU, by rw [hS]; exact hw⟩
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ w ∈ U, seg S U w := by
    rw [iUnion_seg_eq_univ S U hmeet']
    trivial
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.1 hx
  obtain ⟨v, hv, rfl⟩ := hJU w hw
  exact Set.mem_iUnion₂.2 ⟨v, hv, hxw⟩

end TerminalSplice
end TorusEven
