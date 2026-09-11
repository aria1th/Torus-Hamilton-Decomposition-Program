-- STATUS: main-path
import TorusEven.Collar.CircuitBlocks
import TorusEven.Collar.PinnedSelection
import TorusEven.Collar.BinarySplit

namespace TorusEven.Collar

open Surgery

variable {C I Y : Type*} [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I]
variable {m : ℕ} [NeZero m] (F : MultitorusFactorization C I m)
variable (frame : Y × ZMod m ≃ (I → ZMod m)) (i : I)
variable (J : Y → ZMod m → Finset F.CircuitLabel)

noncomputable def sourceSelection (x : I → ZMod m) : Finset C :=
  (J (frame.symm x).1 (frame.symm x).2).image Sigma.fst

@[simp] theorem sourceSelection_frame (y : Y) (t : ZMod m) :
    sourceSelection F frame J (frame (y, t)) = (J y t).image Sigma.fst := by
  simp [sourceSelection]

variable (hc : CircuitConsistent F frame)
variable (hJ : ∀ y t, J y t ⊆ F.blockSupport frame i y)

include hc hJ

omit [DecidableEq C] in
theorem selected_support (x : I → ZMod m) :
    J (frame.symm x).1 (frame.symm x).2 ⊆ F.supportAt i x := by
  obtain ⟨⟨y, t⟩, rfl⟩ := frame.surjective x
  simpa only [frame.symm_apply_apply, hc.supportAt F frame i y t] using hJ y t

theorem sourceSelection_subset (x : I → ZMod m) : sourceSelection F frame J x ⊆ F.users x i := by
  rintro c h
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
  exact (F.mem_users _ _ _).mpr
    ((F.mem_supportAt _ _ _).mp (selected_support F frame i J hc hJ x hq)).1

theorem sourceSelection_card (x : I → ZMod m) :
    (sourceSelection F frame J x).card = (J (frame.symm x).1 (frame.symm x).2).card := by
  apply Finset.card_image_iff.mpr
  intro q hq q' hq' heq
  exact F.supportAt_fst_injOn i x (selected_support F frame i J hc hJ x hq)
    (selected_support F frame i J hc hJ x hq') heq

theorem mem_sourceSelection (x : I → ZMod m) (c : C) :
    c ∈ sourceSelection F frame J x ↔ F.labelAt x c ∈ J (frame.symm x).1 (frame.symm x).2 := by
  constructor
  · intro h
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp h
    rw [← heq, F.labelAt_fst_of_mem i x (selected_support F frame i J hc hJ x hq)]
    exact hq
  · intro h
    exact Finset.mem_image.mpr ⟨F.labelAt x c, h, rfl⟩

theorem sourceSelection_pin (active : Finset C)
    (hpin : ∀ y, Disjoint (J y 0) (F.activeColumns active)) (c : C) (ha : c ∈ active) (y : Y) :
    splitVoltage (sourceSelection F frame J) c (frame (y, 0)) = 0 := by
  apply if_neg
  rw [mem_sourceSelection F frame i J hc hJ, frame.symm_apply_apply]
  intro h
  exact Finset.disjoint_left.mp (hpin y) h ((F.mem_activeColumns _ _).mpr ha)

variable [Fintype Y]

open scoped Classical in
theorem sourceSelection_orbit_sum (c : C) (x : I → ZMod m) :
    (∑ z : orbitSet (F.step c) x, splitVoltage (sourceSelection F frame J) c z.val) =
      ((Finset.univ.filter (fun p : Y × ZMod m => F.labelAt x c ∈ J p.1 p.2)).card : ZMod m) := by
  classical
  let q := F.labelAt x c
  let δ := splitVoltage (sourceSelection F frame J) c
  have hentry (z : I → ZMod m) :
      (if z ∈ orbitSet (F.step c) x then δ z else 0) =
        if q ∈ J (frame.symm z).1 (frame.symm z).2 then (1 : ZMod m) else 0 := by
    by_cases hz : z ∈ orbitSet (F.step c) x
    · have hl : F.labelAt z c = q :=
        congrArg (Sigma.mk c) ((circuitOf_eq (F.step c) x z).mpr hz).symm
      simp only [if_pos hz, δ, splitVoltage, mem_sourceSelection F frame i J hc hJ, hl]
    · have hnot : q ∉ J (frame.symm z).1 (frame.symm z).2 := by
        intro hq
        have hl := F.labelAt_fst_of_mem i z (selected_support F frame i J hc hJ z hq)
        have heq : circuitOf (F.step c) z = circuitOf (F.step c) x := by
          change (⟨c, circuitOf (F.step c) z⟩ : F.CircuitLabel) = ⟨c, circuitOf (F.step c) x⟩ at hl
          exact eq_of_heq (Sigma.mk.inj hl).2
        exact hz ((circuitOf_eq _ _ _).mp heq.symm)
      simp only [if_neg hz, if_neg hnot]
  calc
    (∑ z : orbitSet (F.step c) x, δ z.val) =
        ∑ z ∈ Finset.univ.filter (fun z => z ∈ orbitSet (F.step c) x), δ z :=
      (Finset.sum_subtype _ (by simp) δ).symm
    _ = ∑ z, if q ∈ J (frame.symm z).1 (frame.symm z).2 then (1 : ZMod m) else 0 := by
      rw [Finset.sum_filter]
      simp only [hentry]
    _ = ∑ p : Y × ZMod m, if q ∈ J p.1 p.2 then (1 : ZMod m) else 0 :=
      frame.symm.sum_comp (fun p : Y × ZMod m => if q ∈ J p.1 p.2 then (1 : ZMod m) else 0)
    _ = _ := by
      simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter,
        apply_ite, Nat.cast_zero, q]

omit hJ in
open scoped Classical in
theorem sourceSelection_unit (active : Finset C)
    (hsel : Incidence.IsPinnedSelection (F.blockSupport frame i) (F.activeColumns active) J)
    (c : C) :
    UnitCarry (F.step c) (splitVoltage (sourceSelection F frame J) c) := by
  intro x
  rw [sourceSelection_orbit_sum F frame i J hc hsel.subset c x]
  exact hsel.column_unit (F.labelAt x c)

end TorusEven.Collar
