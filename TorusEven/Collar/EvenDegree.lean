-- STATUS: main-path
import TorusEven.Collar.Closure
import TorusEven.Goals
import Shared.RankCycle

namespace TorusEven.Collar

open Surgery

namespace OneDirection

variable {d m : ℕ} [NeZero m] (hd : 0 < d)

def factorization : MultitorusFactorization (Fin d) Unit m where
  width _ := d
  width_pos _ := hd
  direction _ _ := ()
  step _ := Equiv.addRight 1
  step_eq _ _ j := by cases j; simp
  quota _ i := by cases i; simp

def frame : Unit × ZMod m ≃ (Unit → ZMod m) where
  toFun p := fun _ => p.2
  invFun x := ((), x ())
  left_inv p := by cases p with | mk u t => cases u; rfl
  right_inv x := by funext u; cases u; rfl

theorem hamilton (c : Fin d) : Shared.IsSingleCycleMap ((factorization hd (m := m)).step c) :=
  Shared.single_cycle_of_zmod_rank_equiv _ (Equiv.funUnique Unit (ZMod m)) (fun _ => rfl)

theorem consistent : CircuitConsistent (factorization hd) (frame (m := m)) where
  direction _ _ _ _ := rfl
  circuit c _ _ _ := (circuitOf_eq _ _ _).mpr ((hamilton hd c).2 _ _)

noncomputable def labels : Fin d ≃ (factorization hd (m := m)).CircuitLabel :=
  Equiv.ofBijective ((factorization hd).labelAt 0) ⟨((factorization hd).labelAt 0).injective, by
    rintro ⟨c, q⟩
    induction q using Quotient.inductionOn with | _ x =>
      exact ⟨c, congrArg (Sigma.mk c) ((circuitOf_eq _ _ _).mpr ((hamilton hd c).2 0 x))⟩⟩

theorem state (heven : Even d) :
    RelativeCollarState (factorization hd) (frame (m := m)) ∅ ∅ where
  consistent := consistent hd
  separated := by simp [MultitorusFactorization.ActiveSeparated, Set.InjOn]
  marked_zero := by simp
  gap := by simp
  parity i _ := by
    apply Incidence.evenComponents_of_universal_block _ ()
    · rintro ⟨c, q⟩
      induction q using Quotient.inductionOn with | _ x =>
        exact ((factorization hd).mem_supportAt i _ _).mpr
          ⟨Subsingleton.elim _ _, (circuitOf_eq _ _ _).mpr ((hamilton hd c).2 _ _)⟩
    · simpa only [Fintype.card_congr (labels hd (m := m)).symm, Fintype.card_fin] using heven

end OneDirection

end TorusEven.Collar

namespace TorusEven

theorem even_degree_collar : EvenDegreeCollarGoal := by
  intro d m hdEven hd hmEven hm
  haveI : NeZero m := ⟨by omega⟩
  let F := Collar.OneDirection.factorization (m := m) (by omega : 0 < d)
  let R := Collar.Recolouring.identity F ∅ ∅
  apply (Collar.OneDirection.state (m := m) (by omega : 0 < d) hdEven).hamilton_decomposition
    hm hmEven R
  intro c
  change Shared.IsSingleCycleMap (Surgery.patch (F.step c) ∅ (Equiv.refl _))
  rw [Surgery.patch_refl]
  exact Collar.OneDirection.hamilton _ c

end TorusEven
