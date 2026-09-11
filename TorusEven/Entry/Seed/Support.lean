-- STATUS: main-path
import TorusEven.Entry.Seed
import TorusEven.Entry.Defect
import TorusEven.Collar.IncidenceTransport

namespace TorusEven.Entry.Seed

open Collar Surgery

variable (p : ℕ) (hp : 2 ≤ p) {m : ℕ} (heven : Even m)

def corePresent (j : Fin 3) (hw : ZMod m × ZMod m) (q : Fin 4) : Prop :=
  nearRow hw.1 hw.2 (anchorColor q) = j ∧
    (q = 2 → NearCore.baseDefect heven hw = 0) ∧
    (q = 3 → NearCore.baseDefect heven hw = 1)

instance (j : Fin 3) (hw : ZMod m × ZMod m) (q : Fin 4) :
    Decidable (corePresent heven j hw q) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def support (j : Fin 3) (hw : ZMod m × ZMod m) : Finset (Fin 4 ⊕ Shell.Color p) :=
  (Finset.univ.filter (corePresent heven j hw)).map Function.Embedding.inl ∪
    (Finset.univ.filter (fun c => Shell.direction p hp hw.1 hw.2 c = j)).map
      Function.Embedding.inr

@[simp] theorem mem_support_left (j : Fin 3) (hw : ZMod m × ZMod m) (q : Fin 4) :
    Sum.inl q ∈ support p hp heven j hw ↔ corePresent heven j hw q := by
  simp [support]

@[simp] theorem mem_support_right (j : Fin 3) (hw : ZMod m × ZMod m)
    (c : Shell.Color p) :
    Sum.inr c ∈ support p hp heven j hw ↔ Shell.direction p hp hw.1 hw.2 c = j := by
  simp [support]

variable [NeZero m] (hm : 4 ≤ m)
include hm

private theorem core_mem (j : Fin 3) (hw : ZMod m × ZMod m) (q : Fin 4) :
    anchorLabel q ∈ NearCore.factorization.blockSupport xChart j hw ↔
      corePresent heven j hw q := by
  have h0 : circuitOf (NearCore.step (m := m) 0) (xChart (hw, 0)) =
      circuitOf (NearCore.step 0) (anchor 0) :=
    (circuitOf_eq _ _ _).mpr ((NearCore.hamilton hm 0 (Or.inl rfl)).2 _ _)
  have h1 : circuitOf (NearCore.step (m := m) 1) (xChart (hw, 0)) =
      circuitOf (NearCore.step 1) (anchor 1) :=
    (circuitOf_eq _ _ _).mpr ((NearCore.hamilton hm 1 (Or.inr rfl)).2 _ _)
  have hd2 : NearCore.defect heven (anchor (m := m) 2) = 0 := by
    simp [NearCore.defect, NearCore.baseDefect, anchor, height]
  have hd3 : NearCore.defect heven (anchor (m := m) 3) = 1 := by
    have hthree : parityMap heven (3 : ZMod m) = 1 := by
      change parityMap heven ((3 : ℕ) : ZMod m) = 1
      rw [map_natCast]
      rfl
    simp [NearCore.defect, NearCore.baseDefect, anchor, height, hthree,
      show -(2 : ZMod m) + 3 = 1 by ring, ZMod.val_one'' (by omega : m ≠ 1)]
  have hdef : NearCore.defect heven (xChart (hw, 0)) = NearCore.baseDefect heven hw := by
    change NearCore.baseDefect heven (height (xChart (hw, 0)), hw.2) = _
    rw [height_xChart]
  simp only [MultitorusFactorization.blockSupport, MultitorusFactorization.mem_supportAt,
    anchorLabel]
  change (nearRow (height (xChart (hw, 0))) hw.2 (anchorColor q) = j ∧
    circuitOf (NearCore.step (anchorColor q)) (xChart (hw, 0)) =
      circuitOf (NearCore.step (anchorColor q)) (anchor q)) ↔ _
  rw [height_xChart]
  fin_cases q
  · simp [corePresent, anchorColor, h0]
  · simp [corePresent, anchorColor, h1]
  · change (nearRow hw.1 hw.2 2 = j ∧
      circuitOf (NearCore.step 2) (xChart (hw, 0)) =
        circuitOf (NearCore.step 2) (anchor 2)) ↔ corePresent heven j hw 2
    simp [corePresent, anchorColor, circuitOf_eq, NearCore.orbit_defect_iff hm heven,
      hd2, hdef, eq_comm]
  · change (nearRow hw.1 hw.2 2 = j ∧
      circuitOf (NearCore.step 2) (xChart (hw, 0)) =
        circuitOf (NearCore.step 2) (anchor 3)) ↔ corePresent heven j hw 3
    simp [corePresent, anchorColor, circuitOf_eq, NearCore.orbit_defect_iff hm heven,
      hd3, hdef, eq_comm]

theorem mem_blockSupport_left (j : Fin 3) (hw : ZMod m × ZMod m) (q : Fin 4) :
    (labels p hp hm heven).symm (.inl q) ∈
      (factorization p hp).blockSupport xChart j hw ↔ corePresent heven j hw q := by
  change (NearCore.factorization.superposeLabels (Shell.factorization p hp)).symm
    (.inl (anchorLabel q)) ∈
      (NearCore.factorization.superpose (Shell.factorization p hp)).supportAt j
        (xChart (hw, 0)) ↔ _
  rw [MultitorusFactorization.mem_superpose_support_left]
  exact core_mem heven hm j hw q

theorem mem_blockSupport_right (j : Fin 3) (hw : ZMod m × ZMod m) (c : Shell.Color p) :
    (labels p hp hm heven).symm (.inr c) ∈
      (factorization p hp).blockSupport xChart j hw ↔ Shell.direction p hp hw.1 hw.2 c = j := by
  change (NearCore.factorization.superposeLabels (Shell.factorization p hp)).symm
    (.inr ((Shell.labelEquiv p hp hm).symm c)) ∈
      (NearCore.factorization.superpose (Shell.factorization p hp)).supportAt j
        (xChart (hw, 0)) ↔ _
  rw [MultitorusFactorization.mem_superpose_support_right,
    MultitorusFactorization.mem_supportAt]
  have hc : circuitOf ((Shell.factorization p hp).step c) (xChart (hw, 0)) =
      circuitOf ((Shell.factorization p hp).step c) 0 :=
    (circuitOf_eq _ _ _).mpr ((Shell.hamilton p hp hm c).2 _ _)
  change (Shell.direction p hp (height (xChart (hw, 0))) hw.2 c = j ∧
    circuitOf ((Shell.factorization p hp).step c) (xChart (hw, 0)) =
      circuitOf ((Shell.factorization p hp).step c) 0) ↔ _
  simp only [height_xChart, hc, and_true]

theorem support_eq (j : Fin 3) (hw : ZMod m × ZMod m) :
    support p hp heven j hw = ((factorization p hp).blockSupport xChart j hw).map
      (labels p hp hm heven).toEmbedding := by
  ext q
  cases q with
  | inl q => simp only [mem_support_left, Finset.mem_map_equiv,
      mem_blockSupport_left p hp heven hm]
  | inr c => simp only [mem_support_right, Finset.mem_map_equiv,
      mem_blockSupport_right p hp heven hm]

theorem card_support (j : Fin 3) (hw : ZMod m × ZMod m) :
    (support p hp heven j hw).card = ![p - p / 2 + 1, p / 2 + 1, p + 1] j := by
  rw [support_eq p hp heven hm, Finset.card_map,
    MultitorusFactorization.blockSupport, MultitorusFactorization.card_supportAt, width]

theorem evenComponents_iff (j : Fin 3) :
    Incidence.EvenComponents (support p hp heven j) ↔
      Incidence.EvenComponents ((factorization (m := m) p hp).blockSupport xChart j) := by
  have hmem (hw : ZMod m × ZMod m) (q : Fin 4 ⊕ Shell.Color p) :
      q ∈ support p hp heven j hw ↔
        (labels p hp hm heven).symm q ∈ (factorization p hp).blockSupport xChart j hw := by
    rw [support_eq p hp heven hm, Finset.mem_map_equiv]
  constructor
  · exact Incidence.evenComponents_reindex (Equiv.refl _) (labels p hp hm heven).symm hmem
  · apply Incidence.evenComponents_reindex (Equiv.refl _) (labels p hp hm heven)
    intro hw q
    simpa only [Equiv.symm_apply_apply] using (hmem hw (labels p hp hm heven q)).symm

end TorusEven.Entry.Seed
