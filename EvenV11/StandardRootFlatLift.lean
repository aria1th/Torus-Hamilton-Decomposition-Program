import Shared.TorusCayley

namespace EvenV11
namespace StandardRootFlatLift

abbrev RootState (n m : Nat) :=
  Fin n → ZMod m

def torusEquiv (n m : Nat) :
    ZMod m × RootState n m ≃ Shared.TorusVertex (n + 1) m where
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

def rootStep {n m : Nat}
    (i : Fin (n + 1)) (w : RootState n m) : RootState n m :=
  fun j => if i = j.castSucc then w j + 1 else w j

theorem rootStep_sum_castSucc {n m : Nat}
    (i : Fin n) (w : RootState n m) :
    (∑ j : Fin n, rootStep i.castSucc w j)
      = (∑ j : Fin n, w j) + 1 := by
  classical
  calc
    (∑ j : Fin n, rootStep i.castSucc w j)
        = ∑ j : Fin n, (w j + if i = j then (1 : ZMod m) else 0) := by
            apply Finset.sum_congr rfl
            intro j _hj
            by_cases h : i = j
            · subst j
              simp [rootStep]
            · have hcast : i.castSucc ≠ j.castSucc := by
                intro hc
                exact h (Fin.castSucc_injective n hc)
              simp [rootStep, h, hcast]
    _ = (∑ j : Fin n, w j) + ∑ j : Fin n, (if i = j then (1 : ZMod m) else 0) := by
            rw [Finset.sum_add_distrib]
    _ = (∑ j : Fin n, w j) + 1 := by
            simp

theorem rootStep_sum_last {n m : Nat}
    (w : RootState n m) :
    (∑ j : Fin n, rootStep (Fin.last n) w j)
      = ∑ j : Fin n, w j := by
  classical
  have hlast : ∀ j : Fin n, (Fin.last n : Fin (n + 1)) ≠ j.castSucc := by
    intro j h
    exact Fin.castSucc_ne_last j h.symm
  simp [rootStep, hlast]

theorem torusEquiv_step {n m : Nat}
    (i : Fin (n + 1)) (tw : ZMod m × RootState n m) :
    torusEquiv n m tw + Shared.torusBasis (n + 1) m i =
      torusEquiv n m (tw.1 + 1, rootStep i tw.2) := by
  classical
  symm
  funext k
  rcases Fin.eq_castSucc_or_eq_last k with ⟨j, rfl⟩ | rfl
  · simp only [torusEquiv, Equiv.coe_fn_mk,
      Fin.snoc_castSucc, Pi.add_apply, Shared.torusBasis]
    by_cases h : i = j.castSucc
    · rw [rootStep, if_pos h, if_pos h.symm]
    · have h' : j.castSucc ≠ i := h ∘ Eq.symm
      rw [rootStep, if_neg h, if_neg h']
      simp
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp only [torusEquiv, Equiv.coe_fn_mk,
        Fin.snoc_last, Pi.add_apply, Shared.torusBasis]
      have hlast : (Fin.last n : Fin (n + 1)) ≠ j.castSucc :=
        (Fin.castSucc_ne_last j).symm
      simp [rootStep_sum_castSucc, hlast]
    · simp only [torusEquiv, Equiv.coe_fn_mk,
        Fin.snoc_last, Pi.add_apply, Shared.torusBasis]
      rw [rootStep_sum_last]
      simp
      ring_nf

end StandardRootFlatLift
end EvenV11
