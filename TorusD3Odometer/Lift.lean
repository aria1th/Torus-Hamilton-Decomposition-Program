import TorusD3Odometer.Basic
import TorusD4.Lifts
import Mathlib.Dynamics.PeriodicPts.Defs

namespace TorusD3Odometer

open TorusD4


theorem iterate_add_mul_slicePoint
    [Fact (0 < m)]
    {α : Type*} {F : α × ZMod m → α × ZMod m} {T : α → α} {q0 : ZMod m}
    (hreturn : ∀ a, (F^[m]) (slicePoint q0 a) = slicePoint q0 (T a))
    (t r : ℕ) (a : α) :
    (F^[m * t + r]) (slicePoint q0 a) =
      (F^[r]) (slicePoint q0 ((T^[t]) a)) := by
  -- Inlined from the external repository's `Shared.ReturnLift`.
  calc
    (F^[m * t + r]) (slicePoint q0 a)
        = (F^[r]) (((F^[m * t]) (slicePoint q0 a))) := by
            simpa [Nat.add_comm] using
              Function.iterate_add_apply F r (m * t) (slicePoint q0 a)
    _ = (F^[r]) (slicePoint q0 ((T^[t]) a)) := by
          rw [iterate_mul_slicePoint (m := m) (F := F) (T := T)
            (q0 := q0) hreturn t a]

theorem cycleOn_full_of_cycleOn_slice
    [Fact (0 < m)] [NeZero m]
    {α : Type*} [Fintype α]
    {F : α × ZMod m → α × ZMod m} {T : α → α}
    (hstep : ∀ z, (F z).2 = z.2 + 1)
    (hreturn : ∀ a, (F^[m]) (slicePoint (0 : ZMod m) a) = slicePoint (0 : ZMod m) (T a))
    {N : ℕ} [Fact (0 < N)] (hcard : Fintype.card α = N)
    {a : α} (hc : CycleOn N T a) :
    CycleOn (m * N) F (slicePoint (0 : ZMod m) a) := by
  refine ⟨?_, ?_⟩
  · have hinj :
        Function.Injective fun i : Fin (m * N) =>
          ((F^[i.1]) (slicePoint (0 : ZMod m) a)) := by
      intro i j hij
      let ti : ℕ := i.1 / m
      let tj : ℕ := j.1 / m
      let ri : ℕ := i.1 % m
      let rj : ℕ := j.1 % m
      have hm0 : 0 < m := Fact.out
      have hi_decomp : i.1 = m * ti + ri := by
        dsimp [ti, ri]
        exact (Nat.div_add_mod i.1 m).symm
      have hj_decomp : j.1 = m * tj + rj := by
        dsimp [tj, rj]
        exact (Nat.div_add_mod j.1 m).symm
      have hti_lt : ti < N := by
        dsimp [ti]
        have hi_bound : i.1 < N * m := by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using i.2
        exact (Nat.div_lt_iff_lt_mul hm0).2 hi_bound
      have htj_lt : tj < N := by
        dsimp [tj]
        have hj_bound : j.1 < N * m := by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using j.2
        exact (Nat.div_lt_iff_lt_mul hm0).2 hj_bound
      have hri_lt : ri < m := by
        dsimp [ri]
        exact Nat.mod_lt _ hm0
      have hrj_lt : rj < m := by
        dsimp [rj]
        exact Nat.mod_lt _ hm0
      change
        ((F^[i.1]) (slicePoint (0 : ZMod m) a)) =
          ((F^[j.1]) (slicePoint (0 : ZMod m) a)) at hij
      rw [hi_decomp, iterate_add_mul_slicePoint (m := m) (F := F) (T := T)
        (q0 := (0 : ZMod m)) hreturn ti ri a,
        hj_decomp, iterate_add_mul_slicePoint (m := m) (F := F) (T := T)
          (q0 := (0 : ZMod m)) hreturn tj rj a] at hij
      have hsndi :
          (((F^[ri]) (slicePoint (0 : ZMod m) ((T^[ti]) a))).2) = ((ri : ℕ) : ZMod m) := by
        simpa [slicePoint] using
          snd_iterate_add_one (m := m) (F := F) hstep ri
            (slicePoint (0 : ZMod m) ((T^[ti]) a))
      have hsndj :
          (((F^[rj]) (slicePoint (0 : ZMod m) ((T^[tj]) a))).2) = ((rj : ℕ) : ZMod m) := by
        simpa [slicePoint] using
          snd_iterate_add_one (m := m) (F := F) hstep rj
            (slicePoint (0 : ZMod m) ((T^[tj]) a))
      have hcast : ((ri : ℕ) : ZMod m) = ((rj : ℕ) : ZMod m) := by
        calc
          ((ri : ℕ) : ZMod m) = (((F^[ri]) (slicePoint (0 : ZMod m) ((T^[ti]) a))).2) := by
            symm
            exact hsndi
          _ = (((F^[rj]) (slicePoint (0 : ZMod m) ((T^[tj]) a))).2) := congrArg Prod.snd hij
          _ = ((rj : ℕ) : ZMod m) := hsndj
      have hrem_mod : ri % m = rj % m := by
        exact (ZMod.natCast_eq_natCast_iff' ri rj m).1 hcast
      have hrem : ri = rj := by
        rwa [Nat.mod_eq_of_lt hri_lt, Nat.mod_eq_of_lt hrj_lt] at hrem_mod
      have hij_shift :
          (F^[m - ri]) ((F^[ri]) (slicePoint (0 : ZMod m) ((T^[ti]) a))) =
            (F^[m - ri]) ((F^[rj]) (slicePoint (0 : ZMod m) ((T^[tj]) a))) := by
        exact congrArg ((F^[m - ri])) hij
      have hleft :
          (F^[m - ri]) (((F^[ri]) (slicePoint (0 : ZMod m) ((T^[ti]) a)))) =
            slicePoint (0 : ZMod m) ((T^[ti + 1]) a) := by
        calc
          (F^[m - ri]) (((F^[ri]) (slicePoint (0 : ZMod m) ((T^[ti]) a))))
              = (F^[m - ri + ri]) (slicePoint (0 : ZMod m) ((T^[ti]) a)) := by
                  symm
                  simpa using Function.iterate_add_apply F (m - ri) ri
                    (slicePoint (0 : ZMod m) ((T^[ti]) a))
          _ = (F^[m]) (slicePoint (0 : ZMod m) ((T^[ti]) a)) := by
                rw [Nat.sub_add_cancel (Nat.le_of_lt hri_lt)]
          _ = slicePoint (0 : ZMod m) (T ((T^[ti]) a)) := by
                rw [hreturn]
          _ = slicePoint (0 : ZMod m) ((T^[ti + 1]) a) := by
                rw [Function.iterate_succ_apply']
      have hright0 :
          (F^[m - rj]) (((F^[rj]) (slicePoint (0 : ZMod m) ((T^[tj]) a)))) =
            slicePoint (0 : ZMod m) ((T^[tj + 1]) a) := by
        calc
          (F^[m - rj]) (((F^[rj]) (slicePoint (0 : ZMod m) ((T^[tj]) a))))
              = (F^[m - rj + rj]) (slicePoint (0 : ZMod m) ((T^[tj]) a)) := by
                  symm
                  simpa using Function.iterate_add_apply F (m - rj) rj
                    (slicePoint (0 : ZMod m) ((T^[tj]) a))
          _ = (F^[m]) (slicePoint (0 : ZMod m) ((T^[tj]) a)) := by
                rw [Nat.sub_add_cancel (Nat.le_of_lt hrj_lt)]
          _ = slicePoint (0 : ZMod m) (T ((T^[tj]) a)) := by
                rw [hreturn]
          _ = slicePoint (0 : ZMod m) ((T^[tj + 1]) a) := by
                rw [Function.iterate_succ_apply']
      have hright :
          (F^[m - ri]) (((F^[rj]) (slicePoint (0 : ZMod m) ((T^[tj]) a)))) =
            slicePoint (0 : ZMod m) ((T^[tj + 1]) a) := by
        simpa [hrem] using hright0
      have hslice :
          slicePoint (0 : ZMod m) ((T^[ti + 1]) a) =
            slicePoint (0 : ZMod m) ((T^[tj + 1]) a) := by
        calc
          slicePoint (0 : ZMod m) ((T^[ti + 1]) a)
              = (F^[m - ri]) (((F^[ri]) (slicePoint (0 : ZMod m) ((T^[ti]) a)))) := by
                  symm
                  exact hleft
          _ = (F^[m - ri]) (((F^[rj]) (slicePoint (0 : ZMod m) ((T^[tj]) a)))) := hij_shift
          _ = slicePoint (0 : ZMod m) ((T^[tj + 1]) a) := hright
      have ha_eq : (T^[ti + 1]) a = (T^[tj + 1]) a := by
        simpa [slicePoint] using congrArg Prod.fst hslice
      have ht_mod : ti + 1 ≡ tj + 1 [MOD N] :=
        cycleOn_iterate_modEq (N := N) (f := T) (x := a) hc ha_eq
      have ht'_mod : ti ≡ tj [MOD N] := Nat.ModEq.add_right_cancel' 1 <| by
        simpa [Nat.add_comm] using ht_mod
      have ht : ti = tj := by
        simpa [Nat.ModEq, Nat.mod_eq_of_lt hti_lt, Nat.mod_eq_of_lt htj_lt] using ht'_mod
      apply Fin.eq_of_val_eq
      calc
        i.1 = m * ti + ri := hi_decomp
        _ = m * tj + rj := by rw [ht, hrem]
        _ = j.1 := hj_decomp.symm
    exact (Fintype.bijective_iff_injective_and_card _).2
      ⟨hinj, by
        simp [hcard, ZMod.card, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]⟩
  · calc
      (F^[m * N]) (slicePoint (0 : ZMod m) a)
          = slicePoint (0 : ZMod m) ((T^[N]) a) := by
              rw [iterate_mul_slicePoint (m := m) (F := F) (T := T)
                (q0 := (0 : ZMod m)) hreturn N a]
      _ = slicePoint (0 : ZMod m) a := by
            simpa using congrArg (slicePoint (0 : ZMod m)) hc.2

theorem cycleOn_full_of_cycleOn_p0
    [Fact (0 < m)] [NeZero m]
    {F : P0Coord m × ZMod m → P0Coord m × ZMod m} {T : P0Coord m → P0Coord m}
    (hstep : ∀ z, (F z).2 = z.2 + 1)
    (hreturn : ∀ u, (F^[m]) (slicePoint (0 : ZMod m) u) = slicePoint (0 : ZMod m) (T u))
    {u : P0Coord m} (hc : CycleOn (m ^ 2) T u) :
    CycleOn (m ^ 3) F (slicePoint (0 : ZMod m) u) := by
  have hcard : Fintype.card (P0Coord m) = m ^ 2 := by
    simp [P0Coord, ZMod.card, pow_two]
  have hpow2_pos : 0 < m ^ 2 := by
    exact pow_pos Fact.out 2
  letI : Fact (0 < m ^ 2) := ⟨hpow2_pos⟩
  simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    cycleOn_full_of_cycleOn_slice (m := m) (α := P0Coord m)
      (F := F) (T := T) hstep hreturn hcard hc

end TorusD3Odometer
