-- STATUS: main-path
import TorusEven.Entry.LayerSums
import TorusEven.Entry.Rows
import TorusEven.Collar.Circuits

namespace TorusEven.Entry

open Function Collar Surgery

variable {m n : ℕ} [NeZero m] [NeZero n]
variable (δ : ZMod m → ZMod n)

def heightSection (h : ZMod m) : Set (ZMod m × ZMod n) := {p | p.1 = h}

instance heightSectionDecidable (h : ZMod m) : DecidablePred (· ∈ heightSection (n := n) h) :=
  fun p => inferInstanceAs (Decidable (p.1 = h))

def heightSectionEquiv (h : ZMod m) : ZMod n ≃ heightSection (n := n) h where
  toFun w := ⟨(h, w), rfl⟩
  invFun p := p.val.2
  left_inv _ := rfl
  right_inv p := Subtype.ext (Prod.ext p.property.symm rfl)

omit [NeZero m] [NeZero n] in
theorem heightLift_fst_iterate (p : ZMod m × ZMod n) (k : ℕ) :
    ((lift (Equiv.addRight 1) δ)^[k] p).1 = p.1 + (k : ZMod m) := by
  have he : Semiconj Prod.fst (lift (Equiv.addRight 1) δ) (Equiv.addRight 1) := fun _ => rfl
  refine (he.iterate_right k p).trans ?_
  change ((fun x : ZMod m => x + 1)^[k] p.1) = _
  simp [add_right_iterate, nsmul_eq_mul]

omit [NeZero n] in
theorem heightLift_return (h : ZMod m) (w : ZMod n) :
    (lift (Equiv.addRight 1) δ)^[m] (h, w) = (h, w + ∑ t, δ t) := by
  apply Prod.ext
  · simpa using heightLift_fst_iterate δ (h, w) m
  · change ((Shared.skewProductMap (fun t : ZMod m => t + 1)
      (fun t z => z + δ t))^[m] (h, w)).2 = _
    rw [Shared.skewProductMap_snd_iterate, Shared.skewFiberIterate_zmod_add]
    exact congrArg (w + ·) (Shared.skewFiberAdditiveCarry_eq_univ_sum_of_rank_step
      (fun t : ZMod m => t + 1) (Equiv.refl (ZMod m)) δ h (fun _ => rfl))

theorem heightLift_retTime (h : ZMod m) (w : ZMod n) :
    retTime (lift (Equiv.addRight 1) δ) (heightSection h) (h, w) = m := by
  apply retTime_eq_of_first (lift (Equiv.addRight 1) δ) (heightSection h)
    (show (h, w) ∈ heightSection h from rfl) (NeZero.pos m)
  · rw [heightLift_return]
    rfl
  · intro k hk hkm hhit
    change ((lift (Equiv.addRight 1) δ)^[k] (h, w)).1 = h at hhit
    rw [heightLift_fst_iterate] at hhit
    exact cast_ne_zero hk hkm (add_left_cancel (hhit.trans (add_zero h).symm))

theorem heightLift_retPerm (h : ZMod m) :
    Semiconj (heightSectionEquiv (n := n) h) (Equiv.addRight (∑ t, δ t))
      (retPerm (lift (Equiv.addRight 1) δ) (heightSection h)) := by
  intro w
  apply Subtype.ext
  change (h, w + ∑ t, δ t) = ret (lift (Equiv.addRight 1) δ) (heightSection h) (h, w)
  unfold ret
  rw [heightLift_retTime, heightLift_return]

omit [NeZero n] in
theorem heightLift_meets (h : ZMod m) (p : ZMod m × ZMod n) :
    ∃ q ∈ heightSection h, q ∈ orbitSet (lift (Equiv.addRight 1) δ) p := by
  let k := (h - p.1).val
  refine ⟨(lift (Equiv.addRight 1) δ)^[k] p, ?_, k, rfl⟩
  change ((lift (Equiv.addRight 1) δ)^[k] p).1 = h
  rw [heightLift_fst_iterate]
  simp [k]

theorem heightLift_section_orbit (h : ZMod m) (x y : ZMod n) :
    (h, y) ∈ orbitSet (lift (Equiv.addRight 1) δ) (h, x) ↔
      y ∈ orbitSet (Equiv.addRight (∑ t, δ t)) x := by
  exact (orbit_retPerm_iff _ (heightSection h) (heightSectionEquiv h x)
    (heightSectionEquiv h y)).symm.trans
      (orbit_equiv_iff _ _ (heightSectionEquiv h) (heightLift_retPerm δ h) x y)

theorem heightLift_circuitCount : circuitCount (lift (Equiv.addRight 1) δ) =
    circuitCount (Equiv.addRight (∑ t, δ t)) := by
  let S := lift (Equiv.addRight 1) δ
  let U := heightSection (n := n) (0 : ZMod m)
  have hhit (q : Circuit S) : Hits S U q := by
    induction q using Quotient.inductionOn with | _ x =>
      exact (hits_circuitOf S U x).mpr (heightLift_meets δ 0 x)
  let e : Circuit (retPerm S U) ≃ Circuit S :=
    (returnCircuitEquiv S U).trans (Equiv.subtypeUnivEquiv hhit)
  exact (Nat.card_congr e).symm.trans
    (circuitCount_congr _ _ (heightSectionEquiv 0) (heightLift_retPerm δ 0)).symm

end TorusEven.Entry
