-- STATUS: main-path
import TorusEven.Collar.RelativeState

namespace TorusEven.Collar

open Surgery

variable {C I : Type*} [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I]
variable {m : ℕ} [NeZero m] (F : MultitorusFactorization C I m)
variable (active : Finset C) (U : Set (I → ZMod m)) [DecidablePred (· ∈ U)]

structure Recolouring where
  boundary : C → Equiv.Perm U
  routing : U → Equiv.Perm C
  routing_inactive : ∀ u c, c ∉ active → routing u c = c
  head : ∀ c u, F.step c (boundary c u).val = F.step (routing u c) u.val

namespace Recolouring

def identity : Recolouring F active U where
  boundary _ := Equiv.refl U
  routing _ := Equiv.refl C
  routing_inactive _ _ _ := rfl
  head _ _ := rfl

variable {F active U} (R : Recolouring F active U)

omit [DecidableEq C] [Fintype I] [NeZero m] [DecidablePred (· ∈ U)] in
theorem inactive (c : C) (hc : c ∉ active) : R.boundary c = Equiv.refl U := by
  apply Equiv.ext
  intro u
  apply Subtype.ext
  apply (F.step c).injective
  simpa only [R.routing_inactive u c hc] using R.head c u

omit [DecidableEq C] [Fintype I] [NeZero m] [DecidablePred (· ∈ U)] in
theorem routing_active (u : U) (c : C) (hc : c ∈ active) : R.routing u c ∈ active := by
  classical
  by_contra hn
  have heq := (R.routing u).injective (R.routing_inactive u (R.routing u c) hn)
  exact hn (heq.symm ▸ hc)

def factorization : MultitorusFactorization C I m where
  width := F.width
  width_pos := F.width_pos
  direction c x := if hx : x ∈ U then F.direction (R.routing ⟨x, hx⟩ c) x else F.direction c x
  step c := patch (F.step c) U (R.boundary c)
  step_eq c x j := by
    by_cases hx : x ∈ U
    · rw [patch_apply (F.step c) U (R.boundary c) ⟨x, hx⟩, R.head]
      simpa only [dif_pos hx] using F.step_eq (R.routing ⟨x, hx⟩ c) x j
    · rw [patch_outside (F.step c) U (R.boundary c) hx]
      simpa only [dif_neg hx] using F.step_eq c x j
  quota x i := by
    rw [← F.quota x i]
    by_cases hx : x ∈ U
    · simp only [dif_pos hx, Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Equiv.sum_comp (R.routing ⟨x, hx⟩)
        (fun c => if F.direction c x = i then (1 : ℕ) else 0)
    · simp only [dif_neg hx]

variable {Y : Type*} [Fintype Y] {frame : Y × ZMod m ≃ (I → ZMod m)}
variable {reserved : Finset C} (hc : CircuitConsistent F frame)
variable {i : I} (S : BlockSelection F frame i reserved) (hi : 2 ≤ F.width i)
variable (hs : ∀ c ∈ active, GapSupport (F.step c) U (splitVoltage S.sources c))

noncomputable def split : Recolouring (S.factorization hc hi) active (splitMarks U i) where
  boundary c := splitBoundary U i (R.boundary c)
  routing u := R.routing ((splitMarkEquiv U i).symm u)
  routing_inactive u c hc := R.routing_inactive _ c hc
  head c u := by
    obtain ⟨u, rfl⟩ := (splitMarkEquiv U i).surjective u
    simp only [Equiv.symm_apply_apply, splitBoundary_apply, splitMarkEquiv_val]
    by_cases ha : c ∈ active
    · have hz (d : C) (hd : d ∈ active) (v : U) : splitVoltage S.sources d v.val = 0 :=
        voltage_zero_at_marks (F.step d) U _ (hs d hd) v.property
      have hsem := F.split_semiconj i S.sources (F.width i / 2) (by omega) (by omega)
        (S.subset hc) (S.card hc)
      refine (hsem c ((R.boundary c u).val, 0)).symm.trans
        (Eq.trans ?_ (hsem (R.routing u c) (u.val, 0)))
      simp only [Collar.lift_apply, hz c ha (R.boundary c u),
        hz (R.routing u c) (R.routing_active u c ha) u, add_zero, R.head]
    · rw [R.inactive c ha, R.routing_inactive u c ha]
      rfl

theorem split_circuitCount (c : C) :
    circuitCount ((R.split hc S hi hs).factorization.step c) =
      circuitCount (R.factorization.step c) := by
  change circuitCount (patch ((S.factorization hc hi).step c) (splitMarks U i)
    (splitBoundary U i (R.boundary c))) = circuitCount (patch (F.step c) U (R.boundary c))
  by_cases ha : c ∈ active
  · have hsem := F.split_semiconj i S.sources (F.width i / 2) (by omega) (by omega)
      (S.subset hc) (S.card hc) c
    exact (patch_circuitCount_congr (Collar.lift (F.step c) (splitVoltage S.sources c))
      ((S.factorization hc hi).step c) (zeroSection U) (splitMarks U i)
      (splitChart i) hsem (fun p => (mem_splitMarks U i p.1 p.2).symm)
      (boundaryLift U (R.boundary c))).symm.trans
        (relative_transport (F.step c) U _ (S.unit hc c) (hs c ha) (R.boundary c))
  · rw [R.inactive c ha]
    have hnew : splitBoundary U i (Equiv.refl U) = Equiv.refl (splitMarks U i) := by
      apply Equiv.ext
      intro u
      obtain ⟨v, rfl⟩ := (splitMarkEquiv U i).surjective u
      exact splitBoundary_apply U i (Equiv.refl U) v
    rw [hnew, patch_refl, patch_refl]
    exact F.split_circuitCount i S.sources (F.width i / 2) (by omega) (by omega)
      (S.subset hc) (S.card hc) c (S.unit hc c)

theorem split_hamilton (hH : ∀ c, Shared.IsSingleCycleMap (R.factorization.step c)) :
    ∀ c, Shared.IsSingleCycleMap ((R.split hc S hi hs).factorization.step c) := by
  intro c
  apply singleCycle_of_circuitCount_one
  rw [R.split_circuitCount hc S hi hs c]
  exact circuitCount_one_of_singleCycle _ (hH c)

variable (h : RelativeCollarState F frame active U) (S : BlockSelection F frame i active)
variable (hi : 2 ≤ F.width i)

noncomputable def lift : Recolouring (S.factorization h.consistent hi) active (splitMarks U i) :=
  R.split h.consistent S hi (fun c ha => h.gapSupport c ha _ (S.pin h.consistent c ha))

theorem lift_circuitCount (c : C) :
    circuitCount ((R.lift h S hi).factorization.step c) =
      circuitCount (R.factorization.step c) :=
  R.split_circuitCount h.consistent S hi _ c

theorem lift_hamilton (hH : ∀ c, Shared.IsSingleCycleMap (R.factorization.step c)) :
    ∀ c, Shared.IsSingleCycleMap ((R.lift h S hi).factorization.step c) :=
  R.split_hamilton h.consistent S hi _ hH

end Recolouring

end TorusEven.Collar
