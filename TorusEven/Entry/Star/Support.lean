-- STATUS: main-path
import TorusEven.Entry.Star.Return

namespace TorusEven.Entry.Star

open Collar Surgery

variable {m : ℕ} [NeZero m] (hm : 4 ≤ m)

def support (m : ℕ) : Set (Plane m) := Set.range (word (m := m))

noncomputable instance supportDecidable : DecidablePred (· ∈ support m) :=
  fun p => Classical.propDecidable (p ∈ support m)

noncomputable def wordEquiv : (ZMod m × ZMod 2) ≃ support m :=
  Equiv.ofInjective word (word_injective hm)

include hm in
theorem support_card : Nat.card (support m) = 2 * m := by
  rw [← Nat.card_congr (wordEquiv hm)]
  simp [Nat.card_eq_fintype_card, Nat.mul_comm]

theorem zeroPerm_orbit_word (q : ZMod m × ZMod 2) :
    orbitSet (zeroPerm hm) (word q) = support m := by
  have hs : Function.Semiconj word wordStep (zeroPerm hm) := fun x =>
    ((zeroPerm_apply hm (word x)).trans (surgery_word hm x)).symm
  ext p
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨wordStep^[n] q, hs.iterate_right n q⟩
  · rintro ⟨r, rfl⟩
    obtain ⟨n, hn⟩ := wordStep_singleCycle.2 q r
    exact ⟨n, (hs.iterate_right n q).symm.trans (congrArg word hn)⟩

theorem zeroPerm_orbit_card (q : ZMod m × ZMod 2) :
    Nat.card (orbitSet (zeroPerm hm) (word q)) = 2 * m := by
  rw [zeroPerm_orbit_word]
  exact support_card hm

theorem exists_annihilator {d : ℕ} (hd : 2 ≤ d) (hdiv : d ∣ m) :
    ∃ z : ZMod m, z ≠ 0 ∧ (d : ZMod m) * z = 0 := by
  have hpos : 0 < m / d := Nat.div_pos (Nat.le_of_dvd (NeZero.pos m) hdiv) (by omega)
  have hlt : m / d < m := Nat.div_lt_self (NeZero.pos m) (by omega)
  refine ⟨(m / d : ℕ), cast_ne_zero hpos hlt, ?_⟩
  rw [← Nat.cast_mul, Nat.mul_div_cancel' hdiv, ZMod.natCast_self]

theorem translation_meets_support (slope : ZMod m) (z : ZMod m)
    (hz : z ≠ 0) (hsl : slope * z = 0) (p : Plane m) :
    ∃ u ∈ support m, u ∈ orbitSet (Equiv.addRight (1, slope)) p := by
  let v := p.2 - slope * p.1
  have hv : (0, v) ∈ orbitSet (Equiv.addRight (1, slope)) p := by
    refine ⟨(-p.1).val, ?_⟩
    change ((fun q : Plane m => q + (1, slope))^[(-p.1).val] p) = _
    rw [add_right_iterate_apply, nsmul_eq_mul]
    apply Prod.ext <;> simp [v]; ring
  by_cases hv0 : v = 0
  · have hz' : (z, 0) ∈ orbitSet (Equiv.addRight (1, slope)) (0, 0) := by
      refine ⟨z.val, ?_⟩
      change ((fun q : Plane m => q + (1, slope))^[z.val] (0, 0)) = _
      rw [add_right_iterate_apply, nsmul_eq_mul]
      apply Prod.ext <;> simp [mul_comm, hsl]
    rw [hv0] at hv
    refine ⟨(z, 0), ⟨(z, 0), by simp [word, hz]⟩, ?_⟩
    rwa [← orbitSet_eq_of_mem (Equiv.addRight (1, slope)).injective hv]
  · exact ⟨(0, v), ⟨(v, 1), by simp [word, hv0]⟩, hv⟩

theorem voltage_meets_support (heven : Even m) (p : Plane m) :
    ∃ u ∈ support m, u ∈ orbitSet (Equiv.addRight (voltage (m := m) 0)) p := by
  by_cases hd : 3 ∣ m
  · obtain ⟨z, hz, hz3⟩ := exists_annihilator (by decide : 2 ≤ 3) hd
    simpa [voltage, hd] using translation_meets_support (3 : ZMod m) z hz hz3 p
  · obtain ⟨z, hz, hz2⟩ := exists_annihilator (by decide : 2 ≤ 2) heven.two_dvd
    change (2 : ZMod m) * z = 0 at hz2
    have hn : (-2 : ZMod m) * z = 0 := by rw [neg_mul, hz2, neg_zero]
    simpa [voltage, hd] using translation_meets_support (-2 : ZMod m) z hz hn p

noncomputable def boundary : Equiv.Perm (support m) :=
  (wordEquiv hm).symm.trans (wordStep.trans (wordEquiv hm))

theorem boundaryExtension_eq : boundaryExtension (support m) (boundary hm) = zeroPerm hm := by
  apply Equiv.ext
  intro p
  by_cases hp : p ∈ support m
  · obtain ⟨q, rfl⟩ := hp
    have he := boundaryExtension_apply (support m) (boundary hm) (wordEquiv hm q)
    change boundaryExtension (support m) (boundary hm) (word q) = _ at he
    exact he.trans (by
      simp only [boundary, Equiv.trans_apply, Equiv.symm_apply_apply]
      exact ((zeroPerm_apply hm (word q)).trans (surgery_word hm q)).symm)
  · exact (boundaryExtension_outside (support m) (boundary hm) hp).trans
      ((zeroPerm_apply hm p).trans (surgery_zero_outside p hp)).symm

noncomputable def markedReturn : Equiv.Perm (ZMod m × ZMod 2) :=
  wordStep.trans ((wordEquiv hm).trans
    ((retPerm (Equiv.addRight (voltage 0)) (support m)).trans (wordEquiv hm).symm))

theorem markedReturn_word (q : ZMod m × ZMod 2) :
    word (markedReturn hm q) =
      ret (Equiv.addRight (voltage 0)) (support m) (word (wordStep q)) := by
  change (wordEquiv hm ((wordEquiv hm).symm
    (retPerm (Equiv.addRight (voltage 0)) (support m) (wordEquiv hm (wordStep q))))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem return_circuitCount (heven : Even m) :
    circuitCount (returnPerm hm 0) = circuitCount (markedReturn hm) := by
  let T := Equiv.addRight (voltage (m := m) 0)
  have hh (q : Circuit T) : Hits T (support m) q := by
    induction q using Quotient.inductionOn with | _ p =>
      exact (hits_circuitOf T (support m) p).mpr (voltage_meets_support heven p)
  have hz : Nat.card (UnhitCircuit T (support m)) = 0 := by
    letI : IsEmpty (UnhitCircuit T (support m)) := ⟨fun q => q.property (hh q.val)⟩
    simp
  have he : patch T (support m) (boundary hm) = returnPerm hm 0 := by
    rw [patch, boundaryExtension_eq]
    rfl
  have hc := patch_circuitCount T (support m) (boundary hm)
  rw [he, hz, add_zero] at hc
  have hs : Function.Semiconj (wordEquiv hm) (markedReturn hm)
      ((boundary hm).trans (retPerm T (support m))) := by
    intro q
    simp [markedReturn, boundary, T]
  exact hc.trans (circuitCount_congr _ _ (wordEquiv hm) hs).symm

theorem hamilton_of_markedReturn (heven : Even m)
    (h : Shared.IsSingleCycleMap (markedReturn hm)) :
    Shared.IsSingleCycleMap (returnMap (m := m) 0) := by
  have he : (returnPerm hm 0 : Plane m → Plane m) = returnMap 0 := funext (returnPerm_apply hm 0)
  rw [← he]
  apply singleCycle_of_circuitCount_one
  rw [return_circuitCount hm heven]
  exact circuitCount_one_of_singleCycle _ h

end TorusEven.Entry.Star
