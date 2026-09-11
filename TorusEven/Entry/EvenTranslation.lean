-- STATUS: main-path
import TorusEven.Collar.Circuits

namespace TorusEven.Entry

open Surgery

variable {m : ℕ} [NeZero m] (hm : Even m)

def parityMap : ZMod m →+* ZMod 2 := ZMod.castHom hm.two_dvd _

theorem negTwo_orbit_iff (x y : ZMod m) :
    y ∈ orbitSet (Equiv.addRight (-2 : ZMod m)) x ↔ parityMap hm y = parityMap hm x := by
  constructor
  · rintro ⟨k, rfl⟩
    change parityMap hm ((fun z : ZMod m => z + -2)^[k] x) = _
    rw [add_right_iterate_apply, nsmul_eq_mul]
    have htwo : parityMap hm (2 : ZMod m) = 0 := by
      change parityMap hm ((2 : ℕ) : ZMod m) = 0
      rw [map_natCast]
      decide
    simp [htwo]
  · intro h
    have hz : parityMap hm (y - x) = 0 := by simp [h]
    have heven : Even (y - x).val := by
      apply ZMod.natCast_eq_zero_iff_even.mp
      calc
        ((y - x).val : ZMod 2) = parityMap hm ((y - x).val : ZMod m) :=
          (map_natCast (parityMap hm) _).symm
        _ = parityMap hm (y - x) := congrArg (parityMap hm) (ZMod.natCast_zmod_val _)
        _ = 0 := hz
    obtain ⟨k, hk⟩ := heven
    let t := (-(k : ZMod m)).val
    have ht : (t : ZMod m) = -(k : ZMod m) := ZMod.natCast_zmod_val _
    have hy : y - x = (2 : ZMod m) * k := by
      rw [← ZMod.natCast_zmod_val (y - x), hk, Nat.cast_add]
      ring
    refine ⟨t, ?_⟩
    change ((fun z : ZMod m => z + -2)^[t] x) = y
    rw [add_right_iterate_apply, nsmul_eq_mul, ht]
    calc
      x + -(k : ZMod m) * -2 = x + (y - x) := by rw [hy]; ring
      _ = y := by ring

noncomputable def negTwoCircuitEquiv : Circuit (Equiv.addRight (-2 : ZMod m)) ≃ ZMod 2 :=
  Equiv.ofBijective
    (Quotient.lift (parityMap hm) (fun x y h => ((negTwo_orbit_iff hm x y).mp h).symm)) (by
      constructor
      · intro q q' h
        induction q using Quotient.inductionOn with | _ x =>
          induction q' using Quotient.inductionOn with | _ y =>
            exact Quotient.sound ((negTwo_orbit_iff hm x y).mpr h.symm)
      · intro z
        obtain ⟨x, hx⟩ := ZMod.castHom_surjective hm.two_dvd z
        exact ⟨circuitOf _ x, hx⟩)

include hm

theorem negTwo_circuitCount : circuitCount (Equiv.addRight (-2 : ZMod m)) = 2 :=
  (Nat.card_congr (negTwoCircuitEquiv hm)).trans (by simp [Nat.card_eq_fintype_card])

theorem negTwo_representative (x : ZMod m) :
    (0 : ZMod m) ∈ orbitSet (Equiv.addRight (-2 : ZMod m)) x ∨
      (1 : ZMod m) ∈ orbitSet (Equiv.addRight (-2 : ZMod m)) x := by
  rw [negTwo_orbit_iff hm, negTwo_orbit_iff hm]
  simp only [map_zero, map_one]
  generalize h : parityMap hm x = z
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem negTwo_distinct :
    (1 : ZMod m) ∉ orbitSet (Equiv.addRight (-2 : ZMod m)) 0 := by
  rw [negTwo_orbit_iff hm]
  simp

end TorusEven.Entry
