import D7Odd.StageCells

namespace D7Odd

def markedStageCell (m : Nat) (s : Stage) (w : Vec7 m) : Prop :=
  stageCell m s (w - markerVec m (Stage.tauZ m s))

theorem markedStageCell_w0_eq_tau {m : Nat} {s : Stage} {w : Vec7 m}
    (h : markedStageCell m s w) :
    w 0 = Stage.tauZ m s := by
  have h0 := rawCell_w0_zero (m := m) (s := s) h
  change w 0 - markerVec m (Stage.tauZ m s) 0 = 0 at h0
  simpa using sub_eq_zero.mp h0

private theorem eq_zero_eq_neg_one_absurd {m : Nat} {x : ZMod m}
    (hneg : (-1 : ZMod m) ≠ 0) (h0 : x = 0) (hm1 : x = -1) :
    False :=
  hneg (hm1.symm.trans h0)

theorem stageCell_disjoint_raw_same_tau {m : Nat} [NeZero m] (hm : 5 <= m)
    {s t : Stage} {w : Vec7 m}
    (htau : Stage.tau s = Stage.tau t)
    (hs : stageCell m s w) (ht : stageCell m t w) :
    s = t := by
  by_contra hne
  have hneg : (-1 : ZMod m) ≠ 0 := zmod_neg_one_ne_zero_of_ge5 (m := m) hm
  cases s <;> cases t <;> simp [Stage.tau] at hne htau
  all_goals
    first
    | contradiction
    | exact eq_zero_eq_neg_one_absurd hneg (R1b_w2_zero hs) (R3a_w2_neg_one ht)
    | exact eq_zero_eq_neg_one_absurd hneg (R1b_w2_zero hs) (R3b_w2_neg_one ht)
    | exact eq_zero_eq_neg_one_absurd hneg (R1b_w2_zero hs) (R3c_w2_neg_one ht)
    | exact eq_zero_eq_neg_one_absurd hneg (R4a_w2_zero hs) (R3a_w2_neg_one ht)
    | exact eq_zero_eq_neg_one_absurd hneg (R4a_w2_zero hs) (R3b_w2_neg_one ht)
    | exact eq_zero_eq_neg_one_absurd hneg (R4a_w2_zero hs) (R3c_w2_neg_one ht)
    | exact eq_zero_eq_neg_one_absurd hneg (R1b_w2_zero ht) (R3a_w2_neg_one hs)
    | exact eq_zero_eq_neg_one_absurd hneg (R1b_w2_zero ht) (R3b_w2_neg_one hs)
    | exact eq_zero_eq_neg_one_absurd hneg (R1b_w2_zero ht) (R3c_w2_neg_one hs)
    | exact eq_zero_eq_neg_one_absurd hneg (R4a_w2_zero ht) (R3a_w2_neg_one hs)
    | exact eq_zero_eq_neg_one_absurd hneg (R4a_w2_zero ht) (R3b_w2_neg_one hs)
    | exact eq_zero_eq_neg_one_absurd hneg (R4a_w2_zero ht) (R3c_w2_neg_one hs)
    | exact R4a_w4_ne ht (R1b_w4_zero hs)
    | exact R4a_w4_ne hs (R1b_w4_zero ht)
    | exact R3a_w3_ne hs (R3b_w3_zero ht)
    | exact R3a_w3_ne hs (R3c_w3_zero ht)
    | exact R3a_w3_ne ht (R3b_w3_zero hs)
    | exact R3a_w3_ne ht (R3c_w3_zero hs)
    | exact R3b_w5_ne hs (R3c_w5_zero ht)
    | exact R3b_w5_ne ht (R3c_w5_zero hs)
    | exact R1a_w3_ne hs (R4pa_w3_zero ht)
    | exact R1a_w3_ne hs (R4pb_w3_zero ht)
    | exact R1a_w3_ne ht (R4pa_w3_zero hs)
    | exact R1a_w3_ne ht (R4pb_w3_zero hs)
    | exact R4pa_w6_ne hs (R4pb_w6_zero ht)
    | exact R4pa_w6_ne ht (R4pb_w6_zero hs)
    | exact R4b_w6_ne hs (R4c_w6_zero ht)
    | exact R4b_w6_ne ht (R4c_w6_zero hs)
    | exact R2a_w6_ne hs (R2b_w6_zero ht)
    | exact R2a_w6_ne ht (R2b_w6_zero hs)

theorem markedStageCell_disjoint_fixed {m : Nat} [NeZero m] (hm : 5 <= m)
    {s t : Stage} {w : Vec7 m}
    (hs : markedStageCell m s w)
    (ht : markedStageCell m t w) :
    s = t := by
  have htauZ : Stage.tauZ m s = Stage.tauZ m t := by
    exact (markedStageCell_w0_eq_tau (m := m) (s := s) (w := w) hs).symm.trans
      (markedStageCell_w0_eq_tau (m := m) (s := t) (w := w) ht)
  have htau : Stage.tau s = Stage.tau t := Stage.tauZ_inj_of_ge5 (m := m) hm htauZ
  have ht' : stageCell m t (w - markerVec m (Stage.tauZ m s)) := by
    simpa [markedStageCell, htauZ] using ht
  exact stageCell_disjoint_raw_same_tau (m := m) hm htau hs ht'

theorem markedStageCell_ne_empty_inter {m : Nat} [NeZero m] (hm : 5 <= m)
    {s t : Stage} (hst : s ≠ t) :
    Disjoint {w : Vec7 m | markedStageCell m s w}
      {w : Vec7 m | markedStageCell m t w} := by
  rw [Set.disjoint_left]
  intro w hs ht
  exact hst (markedStageCell_disjoint_fixed (m := m) hm hs ht)

def m3MarkerVec : Stage -> Vec7 3
  | .R1a => ![0, 2, 0, 0, 1, 2, 1]
  | .R1b => ![1, 0, 0, 1, 2, 0, 2]
  | .R2a => ![2, 0, 0, 0, 1, 0, 0]
  | .R2b => ![1, 0, 0, 1, 1, 0, 0]
  | .R3a => ![2, 1, 2, 0, 2, 0, 2]
  | .R3b => ![0, 0, 2, 0, 1, 0, 0]
  | .R3c => ![2, 2, 0, 2, 1, 0, 2]
  | .R4a => ![1, 2, 2, 1, 0, 2, 1]
  | .R4b => ![0, 0, 2, 0, 2, 2, 0]
  | .R4c => ![0, 2, 0, 1, 0, 1, 2]
  | .R4pa => ![0, 2, 2, 1, 0, 1, 0]
  | .R4pb => ![0, 1, 0, 2, 2, 0, 1]

def m3MarkedStageCell (s : Stage) (w : Vec7 3) : Prop :=
  stageCell 3 s (w - m3MarkerVec s)

def m3MarkerSource? : Stage -> Option (Fin 7)
  | .R1a => some 3
  | .R1b => some 5
  | .R2a => some 6
  | .R2b => none
  | .R3a => some 3
  | .R3b => some 5
  | .R3c => none
  | .R4a => some 4
  | .R4b => some 6
  | .R4c => none
  | .R4pa => some 6
  | .R4pb => none

set_option linter.style.nativeDecide false in
theorem m3MarkerVec_root (s : Stage) : Root7 3 (m3MarkerVec s) := by
  cases s <;> unfold Root7 sum7 <;> rw [Fin.sum_univ_seven] <;> native_decide

theorem m3MarkerVec_source_zero {s : Stage} {i : Fin 7}
    (h : m3MarkerSource? s = some i) :
    m3MarkerVec s i = 0 := by
  cases s <;> simp [m3MarkerSource?, m3MarkerVec] at h ⊢
  all_goals
    subst i
    rfl

private instance instDecidableStageCell3 (s : Stage) (w : Vec7 3) :
    Decidable (stageCell 3 s w) := by
  cases s <;>
    unfold stageCell R1aCell R1bCell R2aCell R2bCell R3aCell R3bCell R3cCell
      R4aCell R4bCell R4cCell R4paCell R4pbCell <;>
    infer_instance

private instance instDecidableM3MarkedStageCell (s : Stage) (w : Vec7 3) :
    Decidable (m3MarkedStageCell s w) := by
  unfold m3MarkedStageCell
  infer_instance

set_option linter.style.nativeDecide false in
private theorem m3MarkedStageCell_disjoint_fixed_decide :
    ∀ s t : Stage, ∀ w : Vec7 3,
      m3MarkedStageCell s w -> m3MarkedStageCell t w -> s = t := by
  native_decide

theorem m3MarkedStageCell_disjoint_fixed {s t : Stage} {w : Vec7 3}
    (hs : m3MarkedStageCell s w)
    (ht : m3MarkedStageCell t w) :
    s = t :=
  m3MarkedStageCell_disjoint_fixed_decide s t w hs ht

theorem m3MarkedStageCell_ne_empty_inter {s t : Stage} (hst : s ≠ t) :
    Disjoint {w : Vec7 3 | m3MarkedStageCell s w}
      {w : Vec7 3 | m3MarkedStageCell t w} := by
  rw [Set.disjoint_left]
  intro w hs ht
  exact hst (m3MarkedStageCell_disjoint_fixed hs ht)

end D7Odd
