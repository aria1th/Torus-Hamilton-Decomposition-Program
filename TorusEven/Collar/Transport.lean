-- STATUS: main-path
import TorusEven.Collar.SourceSurgery
import TorusEven.Collar.OrbitLift
import TorusEven.Collar.OneGap

namespace TorusEven.Collar

open Function Surgery

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {m : ℕ} [NeZero m]
variable (S : Equiv.Perm α) (U : Set α) [DecidablePred (· ∈ U)]
variable (δ : α → ZMod m)

noncomputable def liftUnhitEquiv (hunit : UnitCarry S δ) :
    UnhitCircuit (lift S δ) (zeroSection U) ≃ UnhitCircuit S U :=
  (liftCircuitEquiv S δ hunit).subtypeEquiv (by
    intro q
    apply not_congr
    constructor
    · rintro ⟨p, hp⟩
      refine ⟨⟨p.val.1, p.property.1⟩, ?_⟩
      exact (liftCircuitEquiv_apply S δ hunit p.val).symm.trans
        (congrArg (liftCircuitEquiv S δ hunit) hp)
    · rintro ⟨u, hu⟩
      refine ⟨zeroEquiv U u, (liftCircuitEquiv S δ hunit).injective ?_⟩
      exact hu)

def boundaryLift (r : Equiv.Perm U) : Equiv.Perm (zeroSection (m := m) U) :=
  (zeroEquiv U).symm.trans (r.trans (zeroEquiv U))

theorem transport_circuitCount (hunit : UnitCarry S δ)
    (hret : ∀ u ∈ U, ret (lift S δ) (zeroSection U) (u, 0) = (ret S U u, 0))
    (r : Equiv.Perm U) :
    circuitCount (patch (lift S δ) (zeroSection U) (boundaryLift U r)) =
      circuitCount (patch S U r) := by
  rw [patch_circuitCount, patch_circuitCount]
  have hc : circuitCount (r.trans (retPerm S U)) =
      circuitCount ((boundaryLift U r).trans (retPerm (lift S δ) (zeroSection U))) := by
    apply circuitCount_congr _ _ (zeroEquiv U)
    intro u
    apply Subtype.ext
    exact (hret (r u).val (r u).property).symm
  rw [hc, Nat.card_congr (liftUnhitEquiv S U δ hunit)]

omit [Fintype α] [DecidableEq α] [NeZero m] in
theorem patch_lift_at_mark (r : Equiv.Perm U) (u : U)
    (hzero : ∀ x ∈ U, δ x = 0) :
    patch (lift S δ) (zeroSection U) (boundaryLift U r) (u.val, 0) =
      (patch S U r u.val, 0) := by
  change lift S δ (boundaryExtension (zeroSection U) (boundaryLift U r) (zeroEquiv U u).val) = _
  rw [boundaryExtension_apply]
  change (S (r u).val, 0 + δ (r u).val) = (S (boundaryExtension U r u.val), 0)
  rw [hzero _ (r u).property, add_zero, boundaryExtension_apply]

end TorusEven.Collar
