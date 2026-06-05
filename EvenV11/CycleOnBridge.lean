import Shared.RankCycle
import TorusD4.Cycles

namespace EvenV11

/-!
Bridge from the older `TorusD4.CycleOn` orbit certificates to the current
`Shared.IsSingleCycleMap` interface used by `EvenV11`.
-/

noncomputable def cycleOnRankEquiv
    {α : Type*} {N : Nat} [NeZero N] {f : α → α} {x : α}
    (hc : TorusD4.CycleOn N f x) : α ≃ ZMod N :=
  (Equiv.ofBijective (fun i : Fin N => (f^[i.1]) x) hc.1).symm.trans
    (ZMod.finEquiv N).toEquiv

theorem cycleOn_orbit_step
    {α : Type*} {N : Nat} [NeZero N] {f : α → α} {x : α}
    (hN : 1 < N) (hc : TorusD4.CycleOn N f x) (i : Fin N) :
    f ((f^[i.1]) x) = (f^[(i + 1).1]) x := by
  have hone : ((1 : Fin N).val) = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt hN
  rw [Fin.val_add, hone]
  have hsucc : f ((f^[i.1]) x) = (f^[i.1 + 1]) x := by
    rw [Function.iterate_succ_apply']
  rw [hsucc]
  by_cases hlt : i.1 + 1 < N
  · rw [Nat.mod_eq_of_lt hlt]
  · have heq : i.1 + 1 = N := by omega
    rw [heq, Nat.mod_self]
    simpa using hc.2

theorem cycleOnRankEquiv_step
    {α : Type*} {N : Nat} [NeZero N] {f : α → α} {x : α}
    (hN : 1 < N) (hc : TorusD4.CycleOn N f x) :
    ∀ y : α, cycleOnRankEquiv hc (f y) = cycleOnRankEquiv hc y + 1 := by
  intro y
  let orbit : Fin N ≃ α :=
    Equiv.ofBijective (fun i : Fin N => (f^[i.1]) x) hc.1
  let i : Fin N := orbit.symm y
  have hy : y = orbit i := by
    simp [i]
  have hstep : f (orbit i) = orbit (i + 1) := by
    change f ((f^[i.1]) x) = (f^[(i + 1).1]) x
    exact cycleOn_orbit_step hN hc i
  calc
    cycleOnRankEquiv hc (f y)
        = cycleOnRankEquiv hc (f (orbit i)) := by rw [hy]
    _ = cycleOnRankEquiv hc (orbit (i + 1)) := by rw [hstep]
    _ = (ZMod.finEquiv N).toEquiv (i + 1) := by
          simp [cycleOnRankEquiv, orbit]
    _ = (ZMod.finEquiv N).toEquiv i + 1 := by
          simp [ZMod.finEquiv]
    _ = cycleOnRankEquiv hc (orbit i) + 1 := by
          simp [cycleOnRankEquiv, orbit]
    _ = cycleOnRankEquiv hc y + 1 := by rw [hy]

theorem isSingleCycleMap_of_cycleOn
    {α : Type*} {N : Nat} [NeZero N] {f : α → α} {x : α}
    (hN : 1 < N) (hc : TorusD4.CycleOn N f x) :
    Shared.IsSingleCycleMap f :=
  Shared.single_cycle_of_zmod_rank_equiv f (cycleOnRankEquiv hc)
    (cycleOnRankEquiv_step hN hc)

end EvenV11
