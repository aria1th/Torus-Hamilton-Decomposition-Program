import TorusD4.Cycles
import Mathlib.Dynamics.PeriodicPts.Defs

namespace TorusD4

variable {α : Type*}

def slicePoint (q0 : ZMod m) (a : α) : α × ZMod m := (a, q0)

theorem cycleOn_iterate_injective {N : ℕ} {f : α → α} {x : α} (hc : CycleOn N f x)
    {i j : ℕ} (hi : i < N) (hj : j < N) (hij : (f^[i]) x = (f^[j]) x) :
    i = j := by
  have hfin : (⟨i, hi⟩ : Fin N) = ⟨j, hj⟩ := by
    exact hc.1.1 (by simpa using hij)
  exact Fin.ext_iff.mp hfin

theorem cycleOn_periodic {N : ℕ} {f : α → α} {x : α} (hc : CycleOn N f x) (n : ℕ) :
    (f^[n + N]) x = (f^[n]) x := by
  calc
    (f^[n + N]) x = (f^[n]) ((f^[N]) x) := by
      simpa using (Function.iterate_add_apply f n N x)
    _ = (f^[n]) x := by rw [hc.2]

theorem cycleOn_iterate_modEq {N : ℕ} [Fact (0 < N)] {f : α → α} {x : α}
    (hc : CycleOn N f x) {i j : ℕ} (hij : (f^[i]) x = (f^[j]) x) :
    i ≡ j [MOD N] := by
  have hperiodic : Function.IsPeriodicPt f N x := hc.2
  have hmod :
      (f^[i % N]) x = (f^[j % N]) x := by
    calc
      (f^[i % N]) x = (f^[i]) x := by
        exact hperiodic.iterate_mod_apply i
      _ = (f^[j]) x := hij
      _ = (f^[j % N]) x := by
        symm
        exact hperiodic.iterate_mod_apply j
  exact cycleOn_iterate_injective hc (Nat.mod_lt _ Fact.out) (Nat.mod_lt _ Fact.out) hmod

theorem cycleOn_iterate_eq_iff_modEq {N : ℕ} [Fact (0 < N)] {f : α → α} {x : α}
    (hc : CycleOn N f x) {i j : ℕ} :
    (f^[i]) x = (f^[j]) x ↔ i ≡ j [MOD N] := by
  constructor
  · exact cycleOn_iterate_modEq hc
  · intro hij
    have hperiodic : Function.IsPeriodicPt f N x := hc.2
    rw [Nat.ModEq] at hij
    calc
      (f^[i]) x = (f^[i % N]) x := by
        symm
        exact hperiodic.iterate_mod_apply i
      _ = (f^[j % N]) x := by
        rw [hij]
      _ = (f^[j]) x := by
        exact hperiodic.iterate_mod_apply j

theorem snd_iterate_add_one {F : α × ZMod m → α × ZMod m}
    (hstep : ∀ z, (F z).2 = z.2 + 1) :
    ∀ n z, (F^[n] z).2 = z.2 + n
  | 0, z => by simp
  | n + 1, z => by
      rw [Function.iterate_succ_apply', hstep, snd_iterate_add_one (F := F) hstep n z]
      have hcast : (((n + 1 : ℕ) : ZMod m)) = (n : ZMod m) + 1 := by
        rw [Nat.cast_add]
        simp
      rw [hcast]
      rw [add_assoc]

theorem iterate_mul_slicePoint [Fact (0 < m)] {F : α × ZMod m → α × ZMod m} {T : α → α}
    {q0 : ZMod m} (hreturn : ∀ a, (F^[m]) (slicePoint q0 a) = slicePoint q0 (T a)) :
    ∀ t a, (F^[m * t]) (slicePoint q0 a) = slicePoint q0 ((T^[t]) a)
  | 0, a => by simp [slicePoint]
  | t + 1, a => by
      calc
        (F^[m * (t + 1)]) (slicePoint q0 a)
            = (F^[m * t]) ((F^[m]) (slicePoint q0 a)) := by
                rw [Nat.mul_succ, Function.iterate_add_apply]
        _ = (F^[m * t]) (slicePoint q0 (T a)) := by rw [hreturn]
        _ = slicePoint q0 ((T^[t]) (T a)) := by
              rw [iterate_mul_slicePoint hreturn t (T a)]
        _ = slicePoint q0 ((T^[t + 1]) a) := by
              simp [Function.iterate_succ_apply]

end TorusD4
