-- STATUS: main-path
import TorusEven.Collar.SplitIncidence

namespace TorusEven.Collar

variable {C I Y : Type*} [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I]
variable [Fintype Y] {m : ℕ} [NeZero m]
variable (F : MultitorusFactorization C I m) (frame : Y × ZMod m ≃ (I → ZMod m))
variable (i : I) (active : Finset C)

open scoped Classical in
structure BlockSelection where
  rows : Y → ZMod m → Finset F.CircuitLabel
  valid : Incidence.IsPinnedSelection (F.blockSupport frame i) (F.activeColumns active) rows

namespace BlockSelection

variable {F frame i active} (S : BlockSelection F frame i active) (hc : CircuitConsistent F frame)

noncomputable def sources : (I → ZMod m) → Finset C := sourceSelection F frame S.rows

include hc

theorem subset (x : I → ZMod m) : S.sources x ⊆ F.users x i := by
  classical
  exact sourceSelection_subset F frame i S.rows hc S.valid.subset x

theorem card (x : I → ZMod m) : (S.sources x).card = F.width i / 2 := by
  classical
  rw [sources, sourceSelection_card F frame i S.rows hc S.valid.subset]
  simpa [MultitorusFactorization.blockSupport] using
    S.valid.card (frame.symm x).1 (frame.symm x).2

theorem unit (c : C) : UnitCarry (F.step c) (splitVoltage S.sources c) := by
  classical
  exact sourceSelection_unit F frame i S.rows hc active S.valid c

theorem pin (c : C) (ha : c ∈ active) (y : Y) : splitVoltage S.sources c (frame (y, 0)) = 0 := by
  classical
  exact sourceSelection_pin F frame i S.rows hc S.valid.subset active S.valid.pinned c ha y

variable (hi : 2 ≤ F.width i)

noncomputable def factorization : MultitorusFactorization C (Option I) m :=
  F.balancedSplit i S.sources hi (S.subset hc) (S.card hc)

noncomputable def labels : (S.factorization hc hi).CircuitLabel ≃ F.CircuitLabel :=
  splitLabelEquiv F i S.sources (F.width i / 2) (by omega) (by omega)
    (S.subset hc) (S.card hc) (S.unit hc)

theorem consistent : CircuitConsistent (S.factorization hc hi) (splitChart i) :=
  split_circuitConsistent F i S.sources (F.width i / 2) (by omega) (by omega)
    (S.subset hc) (S.card hc) (S.unit hc)

noncomputable def childSupport (j : Option I) : Y × ZMod m → Finset F.CircuitLabel := by
  classical
  exact match j with
    | none => fun p => S.rows p.1 p.2
    | some k => if k = i then fun p => F.blockSupport frame i p.1 \ S.rows p.1 p.2
        else fun p => F.blockSupport frame k p.1

theorem childSupport_mem (j : Option I) (p : Y × ZMod m) (q : F.CircuitLabel) :
    (S.labels hc hi).symm q ∈ (S.factorization hc hi).blockSupport (splitChart i) j (frame p) ↔
      q ∈ S.childSupport j p := by
  classical
  refine (split_blockSupport_mem F i S.sources (F.width i / 2) (by omega) (by omega)
    (S.subset hc) (S.card hc) (S.unit hc) j (frame p) q).trans ?_
  have hsupp (k : I) : q ∈ F.blockSupport frame k p.1 ↔
      F.direction q.1 (frame p) = k ∧ F.labelAt (frame p) q.1 = q := by
    rw [← hc.supportAt F frame k p.1 p.2]
    exact F.mem_supportAt_label k (frame p) q
  have hrow : q ∈ S.rows p.1 p.2 → F.labelAt (frame p) q.1 = q :=
    fun h => ((hsupp i).mp (S.valid.subset p.1 p.2 h)).2
  have hmem : q.1 ∈ S.sources (frame p) ↔ F.labelAt (frame p) q.1 ∈ S.rows p.1 p.2 := by
    simpa only [Equiv.symm_apply_apply] using
      mem_sourceSelection F frame i S.rows hc S.valid.subset (frame p) q.1
  by_cases hl : F.labelAt (frame p) q.1 = q
  · rw [hl] at hmem
    cases j with
    | none => simp [splitDirection, hmem, hl, childSupport]
    | some k =>
      by_cases hk : k = i
      · simp [splitDirection, hmem, hl, childSupport, hk, hsupp, and_comm]
      · by_cases hq : q ∈ S.rows p.1 p.2
        · have hd := ((hsupp i).mp (S.valid.subset p.1 p.2 hq)).1
          simp [splitDirection, hmem, hl, childSupport, hk, hsupp, hq, hd, Ne.symm hk]
        · simp [splitDirection, hmem, hl, childSupport, hk, hsupp, hq]
  · have hq : q ∉ S.rows p.1 p.2 := fun h => hl (hrow h)
    cases j with
    | none => simp [hl, childSupport, hq]
    | some k => by_cases hk : k = i <;> simp [hl, childSupport, hq, hsupp, hk]

theorem parity (hm : Even m)
    (hparity : ∀ k, 2 ≤ F.width k → Incidence.EvenComponents (F.blockSupport frame k))
    (j : Option I) (hj : 2 ≤ (S.factorization hc hi).width j) :
    Incidence.EvenComponents ((S.factorization hc hi).blockSupport (splitChart i) j) := by
  classical
  apply Incidence.evenComponents_reindex frame (S.labels hc hi).symm
    (fun p q => (S.childSupport_mem hc hi j p q).symm)
  cases j with
  | none =>
    exact S.valid.selected_evenComponents hm (fun y => by
      simpa [MultitorusFactorization.blockSupport] using hj)
  | some k =>
    by_cases hk : k = i
    · subst k
      have hw : 2 ≤ F.width i - F.width i / 2 := by
        simpa [factorization, MultitorusFactorization.balancedSplit,
          MultitorusFactorization.split, splitWidth] using hj
      have hp := S.valid.complement_evenComponents hm (fun y => by
        simpa [MultitorusFactorization.blockSupport] using hw)
      simpa only [childSupport, if_pos rfl] using hp
    · have hw : 2 ≤ F.width k := by
        simpa [factorization, MultitorusFactorization.balancedSplit,
          MultitorusFactorization.split, splitWidth, hk] using hj
      have hp := Incidence.evenComponents_copied (R := ZMod m)
        (F.blockSupport frame k) (hparity k hw)
      simpa only [childSupport, if_neg hk] using hp

end BlockSelection

end TorusEven.Collar
