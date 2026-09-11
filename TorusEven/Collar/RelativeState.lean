-- STATUS: main-path
import TorusEven.Collar.SelectedSplit
import TorusEven.Collar.RelativeLift
import TorusEven.Collar.MarkedEquiv

namespace TorusEven.Collar

open Surgery

variable {C I Y : Type*} [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I]
variable [Fintype Y] {m : ℕ} [NeZero m]
variable (F : MultitorusFactorization C I m) (frame : Y × ZMod m ≃ (I → ZMod m))
variable (active : Finset C) (U : Set (I → ZMod m)) [DecidablePred (· ∈ U)]

structure RelativeCollarState : Prop where
  consistent : CircuitConsistent F frame
  separated : F.ActiveSeparated active
  marked_zero : ∀ u ∈ U, (frame.symm u).2 = 0
  gap : ∀ c ∈ active, ∀ u ∈ U, ∃ a ∈ U, a ∈ orbitSet (F.step c) u ∧
    ∀ x ∈ orbitSet (F.step c) u, (frame.symm x).2 ≠ 0 → x ∈ openGap (F.step c) U a
  parity : ∀ i, 2 ≤ F.width i → Incidence.EvenComponents (F.blockSupport frame i)

namespace RelativeCollarState

variable {F frame active U} (h : RelativeCollarState F frame active U)

include h

theorem selection (hm : 4 ≤ m) (i : I) (hi : 2 ≤ F.width i) :
    Nonempty (BlockSelection F frame i active) := by
  classical
  obtain ⟨J, hJ⟩ := Incidence.exists_pinnedSelection (F.blockSupport frame i)
    (F.activeColumns active) hm
    (fun y => F.activeColumns_card_le_one active h.separated i (frame (y, 0))) (h.parity i hi)
  exact ⟨⟨J, hJ⟩⟩

omit [DecidableEq C] [Fintype Y] in
theorem gapSupport (c : C) (hc : c ∈ active) (δ : (I → ZMod m) → ZMod m)
    (hpin : ∀ y, δ (frame (y, 0)) = 0) : GapSupport (F.step c) U δ := by
  intro u hu
  obtain ⟨a, ha, hau, hg⟩ := h.gap c hc u hu
  refine ⟨a, ha, hau, fun x hx hδ => hg x hx ?_⟩
  intro ht
  have he : frame ((frame.symm x).1, 0) = x := by
    rw [← ht]
    exact frame.apply_symm_apply x
  exact hδ (he ▸ hpin (frame.symm x).1)

end RelativeCollarState

variable (i : I)

def splitMarks : Set (Option I → ZMod m) :=
  {z | ((splitChart i).symm z).1 ∈ U ∧ ((splitChart i).symm z).2 = 0}

instance splitMarksDecidable : DecidablePred (· ∈ splitMarks U i) := fun z =>
  inferInstanceAs (Decidable (((splitChart i).symm z).1 ∈ U ∧ ((splitChart i).symm z).2 = 0))

omit [Fintype I] [NeZero m] [DecidablePred (· ∈ U)] in
@[simp] theorem mem_splitMarks (x : I → ZMod m) (t : ZMod m) :
    splitChart i (x, t) ∈ splitMarks U i ↔ x ∈ U ∧ t = 0 := by simp [splitMarks]

def splitZeroEquiv : zeroSection (m := m) U ≃ splitMarks U i :=
  (splitChart i).subtypeEquiv (fun p => (mem_splitMarks U i p.1 p.2).symm)

def splitBoundary (r : Equiv.Perm U) : Equiv.Perm (splitMarks U i) :=
  (splitZeroEquiv U i).permCongr (boundaryLift U r)

def splitMarkEquiv : U ≃ splitMarks U i :=
  (zeroEquiv U).trans (splitZeroEquiv U i)

omit [Fintype I] [NeZero m] [DecidablePred (· ∈ U)] in
@[simp] theorem splitMarkEquiv_val (u : U) :
    (splitMarkEquiv U i u).val = splitChart i (u.val, 0) := rfl

omit [Fintype I] [NeZero m] [DecidablePred (· ∈ U)] in
@[simp] theorem splitBoundary_apply (r : Equiv.Perm U) (u : U) :
    splitBoundary U i r (splitMarkEquiv U i u) = splitMarkEquiv U i (r u) := by
  simp only [splitBoundary, splitMarkEquiv, Equiv.trans_apply,
    Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rfl

namespace RelativeCollarState

variable {F frame active U i} (h : RelativeCollarState F frame active U)
variable (S : BlockSelection F frame i active) (hi : 2 ≤ F.width i)

theorem split (hm : Even m) :
    RelativeCollarState (S.factorization h.consistent hi) (splitChart i) active
      (splitMarks U i) := by
  let K := S.sources
  let G := S.factorization h.consistent hi
  have hsem (c : C) : Function.Semiconj (splitChart i) (lift (F.step c) (splitVoltage K c))
      (G.step c) := F.split_semiconj i K (F.width i / 2) (by omega) (by omega)
        (S.subset h.consistent) (S.card h.consistent) c
  have hor (c : C) (p q : (I → ZMod m) × ZMod m) :
      splitChart i q ∈ orbitSet (G.step c) (splitChart i p) ↔ q.1 ∈ orbitSet (F.step c) p.1 :=
    split_orbit_iff F i K (F.width i / 2) (by omega) (by omega)
      (S.subset h.consistent) (S.card h.consistent) (S.unit h.consistent) c p q
  refine ⟨S.consistent h.consistent hi, ?_, fun _ hu => hu.2, ?_,
    S.parity h.consistent hi hm h.parity⟩
  · exact F.split_activeSeparated i K (F.width i / 2) (by omega) (by omega)
      (S.subset h.consistent) (S.card h.consistent) active h.separated
  · intro c hc u hu
    obtain ⟨⟨x, t⟩, rfl⟩ := (splitChart i).surjective u
    obtain ⟨hx, rfl⟩ := (mem_splitMarks U i x t).mp hu
    have hs := h.gapSupport c hc (splitVoltage K c) (S.pin h.consistent c hc)
    obtain ⟨a, ha, hau, hg⟩ := relative_renewal (F.step c) U (splitVoltage K c)
      (S.unit h.consistent c) hs hx
    refine ⟨splitChart i (a, 0), (mem_splitMarks U i a 0).mpr ⟨ha, rfl⟩,
      (hor c (x, 0) (a, 0)).mpr hau, ?_⟩
    intro z hz ht
    obtain ⟨p, rfl⟩ := (splitChart i).surjective z
    have hp : p.2 ≠ 0 := by simpa only [Equiv.symm_apply_apply] using ht
    exact openGap_map (lift (F.step c) (splitVoltage K c)) (zeroSection U) (G.step c)
      (splitMarks U i) (splitChart i) (hsem c) (fun q => (mem_splitMarks U i q.1 q.2).symm)
      ⟨ha, rfl⟩ (hg p.1 ((hor c (x, 0) p).mp hz) p.2 hp)

theorem transport (c : C) (hc : c ∈ active) (r : Equiv.Perm U) :
    circuitCount (patch ((S.factorization h.consistent hi).step c) (splitMarks U i)
      (splitBoundary U i r)) =
      circuitCount (patch (F.step c) U r) := by
  have hsem := F.split_semiconj i S.sources (F.width i / 2) (by omega) (by omega)
    (S.subset h.consistent) (S.card h.consistent) c
  exact (patch_circuitCount_congr (lift (F.step c) (splitVoltage S.sources c))
    ((S.factorization h.consistent hi).step c) (zeroSection U) (splitMarks U i)
    (splitChart i) hsem (fun p => (mem_splitMarks U i p.1 p.2).symm) (boundaryLift U r)).symm.trans
      (relative_transport (F.step c) U (splitVoltage S.sources c) (S.unit h.consistent c)
        (h.gapSupport c hc _ (S.pin h.consistent c hc)) r)

end RelativeCollarState

end TorusEven.Collar
