-- STATUS: main-path
import TorusEven.Collar.RelativeLift

namespace TorusEven.Collar

open Surgery

variable {Y : Type*} [Fintype Y] [DecidableEq Y]
variable {m : ℕ} [NeZero m]
variable (S : Equiv.Perm (Y × ZMod m)) (U : Set (Y × ZMod m))
variable [DecidablePred (· ∈ U)]

structure FibreGap : Prop where
  marked_zero : ∀ u ∈ U, u.2 = 0
  gap : ∀ u ∈ U, ∃ a ∈ U, a ∈ orbitSet S u ∧
    ∀ x ∈ orbitSet S u, x.2 ≠ 0 → x ∈ openGap S U a

variable (δ : Y × ZMod m → ZMod m)

theorem FibreGap.support (h : FibreGap S U) (hpin : ∀ y, δ (y, 0) = 0) :
    GapSupport S U δ := by
  intro u hu
  obtain ⟨a, ha, hau, hgap⟩ := h.gap u hu
  refine ⟨a, ha, hau, fun x hx hδ => hgap x hx ?_⟩
  intro ht
  exact hδ ((congrArg (fun t => δ (x.1, t)) ht).trans (hpin x.1))

theorem FibreGap.lift_preserves (h : FibreGap S U) (hpin : ∀ y, δ (y, 0) = 0)
    (hunit : UnitCarry S δ) : FibreGap (lift S δ) (zeroSection U) := by
  refine ⟨fun _ hu => hu.2, ?_⟩
  rintro ⟨u, t⟩ ⟨hu, rfl⟩
  obtain ⟨a, ha, hau, hgap⟩ := relative_renewal S U δ hunit (h.support S U δ hpin) hu
  refine ⟨(a, 0), ⟨ha, rfl⟩, (lift_orbit_iff S δ hunit _ _).mpr hau, ?_⟩
  intro x hx ht
  exact hgap x.1 ((lift_orbit_iff S δ hunit _ _).mp hx) x.2 ht

theorem FibreGap.transport (h : FibreGap S U) (hpin : ∀ y, δ (y, 0) = 0)
    (hunit : UnitCarry S δ) (r : Equiv.Perm U) :
    circuitCount (patch (lift S δ) (zeroSection U) (boundaryLift U r)) =
      circuitCount (patch S U r) :=
  relative_transport S U δ hunit (h.support S U δ hpin) r

end TorusEven.Collar
