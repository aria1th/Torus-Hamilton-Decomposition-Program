-- STATUS: main-path
import TorusEven.Entry.Anchors

namespace TorusEven.Entry

open Collar Surgery

variable {m : ℕ} [NeZero m]

theorem anchorLabel_eq_iff (c : Fin 3) (u : Point m) (q : Fin 4) :
    anchorLabel q = (⟨c, circuitOf (NearCore.step c) u⟩ : NearCore.factorization.CircuitLabel) ↔
      anchorColor q = c ∧ anchor q ∈ orbitSet (NearCore.step c) u := by
  constructor
  · intro h
    have hc := congrArg Sigma.fst h
    change anchorColor q = c at hc
    subst c
    have he : circuitOf (NearCore.step (anchorColor q)) (anchor q) =
        circuitOf (NearCore.step (anchorColor q)) u := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    exact ⟨rfl, (circuitOf_eq _ _ _).mp he.symm⟩
  · rintro ⟨rfl, h⟩
    exact congrArg (Sigma.mk (anchorColor q)) ((circuitOf_eq _ _ _).mpr h).symm

def anchorVoltage (c : Fin 3) (v : Point m) : ZMod m :=
  if ∃ q : Fin 4, anchorColor q = c ∧ anchor q = v then 1 else 0

variable (hm : 4 ≤ m) (heven : Even m)

include hm heven

theorem anchorVoltage_single (c : Fin 3) : SingleVoltage (NearCore.step (m := m) c)
    (anchorVoltage c) := by
  intro u
  obtain ⟨q, hq⟩ := (anchorEquiv hm heven).surjective ⟨c, circuitOf (NearCore.step c) u⟩
  change anchorLabel q = _ at hq
  obtain ⟨hc, horb⟩ := (anchorLabel_eq_iff c u q).mp hq
  refine ⟨anchor q, horb, fun x hx => ?_⟩
  have hiff : (∃ r : Fin 4, anchorColor r = c ∧ anchor r = x) ↔ x = anchor q := by
    constructor
    · rintro ⟨r, hrc, hrx⟩
      have hr : anchorLabel r = (⟨c, circuitOf (NearCore.step c) u⟩ :
          NearCore.factorization.CircuitLabel) :=
        (anchorLabel_eq_iff c u r).mpr ⟨hrc, hrx ▸ hx⟩
      exact hrx.symm.trans (congrArg anchor (anchorLabel_injective hm heven (hr.trans hq.symm)))
    · intro h
      exact ⟨q, hc, h.symm⟩
  simp only [anchorVoltage, hiff]

theorem anchorVoltage_unit (c : Fin 3) : UnitCarry (NearCore.step (m := m) c)
    (anchorVoltage c) := (anchorVoltage_single hm heven c).unit _ _

theorem anchorVoltage_gapSupport (c : Fin 3) : GapSupport (NearCore.step (m := m) c)
    (replacementSupport m) (anchorVoltage c) := by
  apply gapSupport_of_single_source
  intro u _hu
  obtain ⟨q, hq⟩ := (anchorEquiv hm heven).surjective ⟨c, circuitOf (NearCore.step c) u⟩
  change anchorLabel q = _ at hq
  obtain ⟨hc, horb⟩ := (anchorLabel_eq_iff c u q).mp hq
  refine ⟨anchor q, horb, anchor_outside hm q, fun x hx hn => ?_⟩
  have hsrc : ∃ r : Fin 4, anchorColor r = c ∧ anchor r = x := by
    by_contra h
    exact hn (if_neg h)
  obtain ⟨r, hrc, hrx⟩ := hsrc
  have hr := (anchorLabel_eq_iff c u r).mpr ⟨hrc, hrx ▸ hx⟩
  exact hrx.symm.trans (congrArg anchor (anchorLabel_injective hm heven (hr.trans hq.symm)))

end TorusEven.Entry
