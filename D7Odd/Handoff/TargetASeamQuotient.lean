import D7Odd.Handoff.ReturnCriterion

namespace D7Odd
namespace Handoff

/-!
Lean-facing interface for the Target-A `23/32` seam quotient.

The current proof notes reduce the generic `23/32` primitive block to an
arithmetic quotient on `{1,...,h}`.  This file records that quotient as a
formal proof target.  It does not assert the theorem unconditionally; the
missing arithmetic proof is packaged as `TargetASeamQuotientArithmetic`.
-/

namespace TargetA

def phiNat (h x : Nat) : Nat :=
  if x < 3 then
    (x + h - 3) % h
  else if x < 5 then
    (x + h - 8) % h
  else
    (x + h - 5) % h

def phi (h : Nat) [NeZero h] : Fin h → Fin h :=
  fun x => ⟨phiNat h x.val, by
    unfold phiNat
    split
    · exact Nat.mod_lt _ (NeZero.pos h)
    · split
      · exact Nat.mod_lt _ (NeZero.pos h)
      · exact Nat.mod_lt _ (NeZero.pos h)⟩

def phiInvNat (h x : Nat) : Nat :=
  if x + 5 < h then
    (x + 5) % h
  else if x + 5 = h then
    3 % h
  else if x + 4 = h then
    4 % h
  else if x + 3 = h then
    0
  else if x + 2 = h then
    1 % h
  else
    2 % h

def phiInv (h : Nat) [NeZero h] : Fin h → Fin h :=
  fun x => ⟨phiInvNat h x.val, by
    unfold phiInvNat
    split
    · exact Nat.mod_lt _ (NeZero.pos h)
    · split
      · exact Nat.mod_lt _ (NeZero.pos h)
      · split
        · exact Nat.mod_lt _ (NeZero.pos h)
        · split
          · exact Nat.zero_lt_of_lt (NeZero.pos h)
          · split
            · exact Nat.mod_lt _ (NeZero.pos h)
            · exact Nat.mod_lt _ (NeZero.pos h)⟩

def residueShift (h : Nat) : ZMod 5 :=
  (3 : ZMod 5) - h

def goodPhiClass (h : Nat) : Prop :=
  h % 5 ≠ 3

theorem residueShift_eq_zero_iff (h : Nat) :
    residueShift h = 0 ↔ h % 5 = 3 := by
  constructor
  · intro hzero
    have hcast : ((h : Nat) : ZMod 5) = (3 : ZMod 5) := by
      unfold residueShift at hzero
      linear_combination -hzero
    have hmodeq : h ≡ 3 [MOD 5] :=
      (ZMod.natCast_eq_natCast_iff h 3 5).1 hcast
    have hmodeq' : h % 5 ≡ 3 [MOD 5] :=
      (Nat.mod_modEq h 5).trans hmodeq
    exact hmodeq'.eq_of_lt_of_lt (Nat.mod_lt h (by decide)) (by decide)
  · intro hmod
    have hmodeq_mod : h % 5 ≡ 3 [MOD 5] := by
      rw [hmod]
    have hmodeq : h ≡ 3 [MOD 5] :=
      (Nat.mod_modEq h 5).symm.trans hmodeq_mod
    have hcast : ((h : Nat) : ZMod 5) = (3 : ZMod 5) :=
      (ZMod.natCast_eq_natCast_iff h 3 5).2 hmodeq
    unfold residueShift
    rw [hcast]
    simp

theorem natCast_zmod5_eq_mod (h : Nat) :
    ((h : Nat) : ZMod 5) = ((h % 5 : Nat) : ZMod 5) := by
  apply (ZMod.natCast_eq_natCast_iff h (h % 5) 5).2
  exact (Nat.mod_modEq h 5).symm

theorem residueShift_isUnit_iff_goodPhiClass (h : Nat) :
    IsUnit (residueShift h) ↔ goodPhiClass h := by
  haveI : Fact (1 < 5) := ⟨by decide⟩
  constructor
  · intro hunit hbad
    have hshift0 : residueShift h = 0 := (residueShift_eq_zero_iff h).2 hbad
    rw [hshift0] at hunit
    exact (not_isUnit_zero (M₀ := ZMod 5)) hunit
  · intro hgood
    have hcases :
        h % 5 = 0 ∨ h % 5 = 1 ∨ h % 5 = 2 ∨
          h % 5 = 3 ∨ h % 5 = 4 := by
      have hlt := Nat.mod_lt h (by decide : 0 < 5)
      omega
    have hcast := natCast_zmod5_eq_mod h
    rcases hcases with h0 | h1 | h2 | h3 | h4
    · unfold residueShift
      rw [hcast, h0]
      change IsUnit (3 : ZMod 5)
      exact (ZMod.unitOfCoprime 3
        (by decide : Nat.Coprime 3 5)).isUnit
    · unfold residueShift
      rw [hcast, h1]
      change IsUnit (2 : ZMod 5)
      exact (ZMod.unitOfCoprime 2
        (by decide : Nat.Coprime 2 5)).isUnit
    · unfold residueShift
      rw [hcast, h2]
      change IsUnit (1 : ZMod 5)
      exact (ZMod.unitOfCoprime 1
        (by decide : Nat.Coprime 1 5)).isUnit
    · exact False.elim (hgood h3)
    · unfold residueShift
      rw [hcast, h4]
      change IsUnit (4 : ZMod 5)
      exact (ZMod.unitOfCoprime 4
        (by decide : Nat.Coprime 4 5)).isUnit

theorem residueShift_ne_zero_iff_goodPhiClass (h : Nat) :
    residueShift h ≠ 0 ↔ goodPhiClass h := by
  rw [goodPhiClass]
  constructor
  · intro hne hbad
    exact hne ((residueShift_eq_zero_iff h).2 hbad)
  · intro hgood hzero
    exact hgood ((residueShift_eq_zero_iff h).1 hzero)

theorem residueShift_eq_zero_of_bad {h : Nat} (hbad : h % 5 = 3) :
    residueShift h = 0 :=
  (residueShift_eq_zero_iff h).2 hbad

theorem residueShift_ne_zero_of_good {h : Nat} (hgood : goodPhiClass h) :
    residueShift h ≠ 0 :=
  (residueShift_ne_zero_iff_goodPhiClass h).2 hgood

theorem zmod_add_single_cycle_of_isUnit
    {m : Nat} [NeZero m] {a : ZMod m} (ha : IsUnit a) :
    IsSingleCycleMap (fun x : ZMod m => x + a) := by
  rcases ha with ⟨u, rfl⟩
  let rank : ZMod m → ZMod m := Units.mulLeft u⁻¹
  have hrank : Function.Bijective rank := by
    exact Equiv.bijective (Units.mulLeft u⁻¹)
  have hstep : ∀ x, rank (x + (u : ZMod m)) = rank x + 1 := by
    intro x
    dsimp [rank]
    rw [mul_add]
    rw [show (↑u⁻¹ : ZMod m) * (u : ZMod m) = 1 by simp]
  have hf_inj : Function.Injective (fun x : ZMod m => x + (u : ZMod m)) := by
    intro x y hxy
    apply hrank.1
    have h : rank x + (1 : ZMod m) = rank y + 1 := by
      simpa [hstep x, hstep y] using congrArg rank hxy
    exact add_right_cancel h
  have hf_surj : Function.Surjective (fun x : ZMod m => x + (u : ZMod m)) := by
    intro y
    let target : ZMod m := rank y - 1
    rcases hrank.2 target with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply hrank.1
    calc
      rank (x + (u : ZMod m)) = rank x + 1 := hstep x
      _ = target + 1 := by rw [hx]
      _ = rank y := by simp [target]
  refine ⟨⟨hf_inj, hf_surj⟩, ?_⟩
  intro x y
  rcases ZMod.natCast_zmod_surjective (rank y - rank x) with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  apply hrank.1
  calc
    rank (((fun x : ZMod m => x + (u : ZMod m))^[n]) x) =
        rank x + (n : ZMod m) :=
      Shared.iterate_rank_add_one _ rank hstep n x
    _ = rank x + (rank y - rank x) := by rw [hn]
    _ = rank y := by ring

theorem residueShift_add_single_cycle_of_good {h : Nat}
    (hgood : goodPhiClass h) :
    IsSingleCycleMap (fun r : ZMod 5 => r + residueShift h) := by
  exact zmod_add_single_cycle_of_isUnit
    ((residueShift_isUnit_iff_goodPhiClass h).2 hgood)

theorem phiInvNat_of_add_five_lt {h x : Nat} (hx : x + 5 < h) :
    phiInvNat h x = x + 5 := by
  unfold phiInvNat
  rw [if_pos hx]
  exact Nat.mod_eq_of_lt hx

theorem phiInv_iterate_internal_val {h : Nat} [NeZero h] {x n : Nat}
    (hxn : x + 5 * n < h) :
    (((phiInv h)^[n]) (⟨x, by omega⟩ : Fin h)).val = x + 5 * n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hxnext : x + 5 * n < h := by omega
      have ihx := ih hxnext
      have hinternal : x + 5 * n + 5 < h := by
        simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hxn
      apply Eq.trans ?_ (show x + 5 * (n + 1) = x + 5 * n + 5 by omega).symm
      rw [show ((phiInv h)^[n]) (⟨x, by omega⟩ : Fin h) =
          (⟨x + 5 * n, hxnext⟩ : Fin h) by
        apply Fin.ext
        exact ihx]
      change phiInvNat h (x + 5 * n) = x + 5 * n + 5
      exact phiInvNat_of_add_five_lt hinternal

theorem phiInv_reaches_internal_target {h : Nat} [NeZero h] {x y : Nat}
    (hxy : x ≤ y) (hmod : (y : ZMod 5) = (x : ZMod 5)) (hy : y < h) :
    ∃ n, ((phiInv h)^[n]) (⟨x, by omega⟩ : Fin h) = (⟨y, hy⟩ : Fin h) := by
  have hmodeq : y ≡ x [MOD 5] := (ZMod.natCast_eq_natCast_iff y x 5).1 hmod
  have hdiv : 5 ∣ y - x := by
    rw [Nat.ModEq] at hmodeq
    exact Nat.dvd_of_mod_eq_zero (by omega : (y - x) % 5 = 0)
  rcases hdiv with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  apply Fin.ext
  have hy_eq : y = x + 5 * n := by omega
  subst y
  exact phiInv_iterate_internal_val (h := h) (x := x) (n := n) hy

theorem phiInv_reaches_boundary_jump_val {h : Nat} [NeZero h] {x y : Nat}
    (hxy : x ≤ y) (hmod : (y : ZMod 5) = (x : ZMod 5))
    (hy : y < h) :
    ∃ n, (((phiInv h)^[n]) (⟨x, by omega⟩ : Fin h)).val =
      phiInvNat h y := by
  rcases phiInv_reaches_internal_target (h := h) (x := x) (y := y)
      hxy hmod hy with ⟨n, hn⟩
  refine ⟨n + 1, ?_⟩
  rw [Function.iterate_succ_apply']
  rw [hn]
  rfl

theorem phiInvNat_top_five {h : Nat} (hh : 6 ≤ h) :
    phiInvNat h (h - 5) = 3 := by
  unfold phiInvNat
  have hnot : ¬ (h - 5 + 5 < h) := by omega
  have hyes : h - 5 + 5 = h := by omega
  rw [if_neg hnot, if_pos hyes]
  exact Nat.mod_eq_of_lt (by omega : 3 < h)

theorem phiInvNat_top_four {h : Nat} (hh : 6 ≤ h) :
    phiInvNat h (h - 4) = 4 := by
  unfold phiInvNat
  have hnot1 : ¬ (h - 4 + 5 < h) := by omega
  have hnot2 : ¬ (h - 4 + 5 = h) := by omega
  have hyes : h - 4 + 4 = h := by omega
  rw [if_neg hnot1, if_neg hnot2, if_pos hyes]
  exact Nat.mod_eq_of_lt (by omega : 4 < h)

theorem phiInvNat_top_three {h : Nat} (hh : 6 ≤ h) :
    phiInvNat h (h - 3) = 0 := by
  unfold phiInvNat
  have hnot1 : ¬ (h - 3 + 5 < h) := by omega
  have hnot2 : ¬ (h - 3 + 5 = h) := by omega
  have hnot3 : ¬ (h - 3 + 4 = h) := by omega
  have hyes : h - 3 + 3 = h := by omega
  simp [hnot1, hnot2, hnot3, hyes]

theorem phiInvNat_top_two {h : Nat} (hh : 6 ≤ h) :
    phiInvNat h (h - 2) = 1 := by
  unfold phiInvNat
  have hnot1 : ¬ (h - 2 + 5 < h) := by omega
  have hnot2 : ¬ (h - 2 + 5 = h) := by omega
  have hnot3 : ¬ (h - 2 + 4 = h) := by omega
  have hnot4 : ¬ (h - 2 + 3 = h) := by omega
  have hyes : h - 2 + 2 = h := by omega
  simp [hnot1, hnot2, hnot3, hnot4, hyes,
    Nat.mod_eq_of_lt (by omega : 1 < h)]

theorem phiInvNat_top_one {h : Nat} (hh : 6 ≤ h) :
    phiInvNat h (h - 1) = 2 := by
  unfold phiInvNat
  have hnot1 : ¬ (h - 1 + 5 < h) := by omega
  have hnot2 : ¬ (h - 1 + 5 = h) := by omega
  have hnot3 : ¬ (h - 1 + 4 = h) := by omega
  have hnot4 : ¬ (h - 1 + 3 = h) := by omega
  have hnot5 : ¬ (h - 1 + 2 = h) := by omega
  simp [hnot1, hnot2, hnot3, hnot4, hnot5,
    Nat.mod_eq_of_lt (by omega : 2 < h)]

theorem phiInvNat_internal_mod_five {h x : Nat} (hx : x + 5 < h) :
    ((phiInvNat h x : Nat) : ZMod 5) = (x : ZMod 5) := by
  rw [phiInvNat_of_add_five_lt hx, Nat.cast_add]
  change (x : ZMod 5) + (5 : ZMod 5) = (x : ZMod 5)
  rw [show (5 : ZMod 5) = 0 by exact ZMod.natCast_self 5]
  simp

theorem phiInvNat_top_mod_five {h x : Nat}
    (hh : 6 ≤ h) (hx : x < h) (hnot : ¬ x + 5 < h) :
    ((phiInvNat h x : Nat) : ZMod 5) =
      (x : ZMod 5) + residueShift h := by
  by_cases h5 : x + 5 = h
  · have hxval : x = h - 5 := by omega
    rw [hxval, phiInvNat_top_five hh]
    unfold residueShift
    rw [Nat.cast_sub (by omega : 5 ≤ h)]
    ring_nf
    try decide
  · by_cases h4 : x + 4 = h
    · have hxval : x = h - 4 := by omega
      rw [hxval, phiInvNat_top_four hh]
      unfold residueShift
      rw [Nat.cast_sub (by omega : 4 ≤ h)]
      ring_nf
      try decide
    · by_cases h3 : x + 3 = h
      · have hxval : x = h - 3 := by omega
        rw [hxval, phiInvNat_top_three hh]
        unfold residueShift
        rw [Nat.cast_sub (by omega : 3 ≤ h)]
        ring_nf
        try decide
      · by_cases h2 : x + 2 = h
        · have hxval : x = h - 2 := by omega
          rw [hxval, phiInvNat_top_two hh]
          unfold residueShift
          rw [Nat.cast_sub (by omega : 2 ≤ h)]
          ring_nf
          try decide
        · have hxval : x = h - 1 := by omega
          rw [hxval, phiInvNat_top_one hh]
          unfold residueShift
          rw [Nat.cast_sub (by omega : 1 ≤ h)]
          ring_nf
          try decide

theorem phiInvNat_mod_five {h x : Nat} (hh : 6 ≤ h) (hx : x < h) :
    ((phiInvNat h x : Nat) : ZMod 5) =
      if x + 5 < h then
        (x : ZMod 5)
      else
        (x : ZMod 5) + residueShift h := by
  by_cases hlt : x + 5 < h
  · rw [if_pos hlt]
    exact phiInvNat_internal_mod_five hlt
  · rw [if_neg hlt]
    exact phiInvNat_top_mod_five hh hx hlt

theorem phiInvNat_boundary_lt_five {h x : Nat}
    (hh : 6 ≤ h) (hx : x < h) (hnot : ¬ x + 5 < h) :
    phiInvNat h x < 5 := by
  by_cases h5 : x + 5 = h
  · have hxval : x = h - 5 := by omega
    rw [hxval, phiInvNat_top_five hh]
    omega
  · by_cases h4 : x + 4 = h
    · have hxval : x = h - 4 := by omega
      rw [hxval, phiInvNat_top_four hh]
      omega
    · by_cases h3 : x + 3 = h
      · have hxval : x = h - 3 := by omega
        rw [hxval, phiInvNat_top_three hh]
        omega
      · by_cases h2 : x + 2 = h
        · have hxval : x = h - 2 := by omega
          rw [hxval, phiInvNat_top_two hh]
          omega
        · have hxval : x = h - 1 := by omega
          rw [hxval, phiInvNat_top_one hh]
          omega

theorem phiInvNat_boundary_residue {h x : Nat}
    (hh : 6 ≤ h) (hx : x < h) (hboundary : ¬ x + 5 < h) :
    ((phiInvNat h x : Nat) : ZMod 5) = (x : ZMod 5) + residueShift h :=
  phiInvNat_top_mod_five hh hx hboundary

theorem phiInv_reaches_boundary_jump_residue {h : Nat} [NeZero h] {x y : Nat}
    (hh : 6 ≤ h) (hxy : x ≤ y) (hmod : (y : ZMod 5) = (x : ZMod 5))
    (hy : y < h) (hboundary : ¬ y + 5 < h) :
    ∃ n, (((((phiInv h)^[n]) (⟨x, by omega⟩ : Fin h)).val : Nat) : ZMod 5) =
      (x : ZMod 5) + residueShift h := by
  rcases phiInv_reaches_boundary_jump_val (h := h) (x := x) (y := y)
      hxy hmod hy with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [hn]
  rw [phiInvNat_boundary_residue hh hy hboundary]
  rw [hmod]

theorem nat_eq_of_zmod5_eq_of_lt {a b : Nat}
    (ha : a < 5) (hb : b < 5) (h : (a : ZMod 5) = (b : ZMod 5)) :
    a = b := by
  have hm : a ≡ b [MOD 5] := (ZMod.natCast_eq_natCast_iff a b 5).1 h
  exact hm.eq_of_lt_of_lt ha hb

theorem phiInv_reaches_boundary_jump_low {h : Nat} [NeZero h] {x y b : Nat}
    (hh : 6 ≤ h) (hxy : x ≤ y) (hmod : (y : ZMod 5) = (x : ZMod 5))
    (hy : y < h) (hboundary : ¬ y + 5 < h) (hb : b < 5)
    (hbmod : (b : ZMod 5) = (x : ZMod 5) + residueShift h) :
    ∃ n, ((phiInv h)^[n]) (⟨x, by omega⟩ : Fin h) =
      (⟨b, by omega⟩ : Fin h) := by
  rcases phiInv_reaches_boundary_jump_val (h := h) (x := x) (y := y)
      hxy hmod hy with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  apply Fin.ext
  have hvalmod : ((phiInvNat h y : Nat) : ZMod 5) =
      (x : ZMod 5) + residueShift h := by
    rw [phiInvNat_boundary_residue hh hy hboundary]
    rw [hmod]
  have heq : phiInvNat h y = b :=
    nat_eq_of_zmod5_eq_of_lt
      (phiInvNat_boundary_lt_five hh hy hboundary) hb
      (by rw [hvalmod, hbmod])
  calc
    (((phiInv h)^[n]) (⟨x, by omega⟩ : Fin h)).val = phiInvNat h y := hn
    _ = b := heq

def laneTop (h x : Nat) : Nat :=
  x + 5 * ((h - 1 - x) / 5)

theorem laneTop_ge (h x : Nat) :
    x ≤ laneTop h x := by
  unfold laneTop
  omega

theorem laneTop_lt {h x : Nat} (hx : x < h) :
    laneTop h x < h := by
  unfold laneTop
  have hmul : 5 * ((h - 1 - x) / 5) ≤ h - 1 - x :=
    Nat.mul_div_le (h - 1 - x) 5
  omega

theorem laneTop_boundary {h x : Nat} (hx : x < h) :
    ¬ laneTop h x + 5 < h := by
  intro hb
  unfold laneTop at hb
  let d := h - 1 - x
  have hdecomp : d % 5 + 5 * (d / 5) = d := Nat.mod_add_div d 5
  have hmodlt : d % 5 < 5 := Nat.mod_lt d (by decide)
  have hlarge : 5 * (d / 5) + 5 ≤ d := by omega
  omega

theorem laneTop_mod_eq {h x : Nat} :
    ((laneTop h x : Nat) : ZMod 5) = (x : ZMod 5) := by
  unfold laneTop
  rw [Nat.cast_add, Nat.cast_mul]
  change (x : ZMod 5) +
    (5 : ZMod 5) * (((h - 1 - x) / 5 : Nat) : ZMod 5) = (x : ZMod 5)
  rw [show (5 : ZMod 5) = 0 by exact ZMod.natCast_self 5]
  simp

theorem phiInv_reaches_next_low {h : Nat} [NeZero h] (hh : 6 ≤ h)
    {x b : Nat} (hx : x < h) (hb : b < 5)
    (hbmod : (b : ZMod 5) = (x : ZMod 5) + residueShift h) :
    ∃ n, ((phiInv h)^[n]) (⟨x, hx⟩ : Fin h) =
      (⟨b, by omega⟩ : Fin h) := by
  rcases phiInv_reaches_boundary_jump_low (h := h) (x := x)
      (y := laneTop h x) (b := b) hh
      (laneTop_ge h x) laneTop_mod_eq (laneTop_lt hx) (laneTop_boundary hx)
      hb hbmod with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa using hn

private theorem add_sub_mod_eq_sub {h x c : Nat} (hc : c ≤ x) (hx : x < h) :
    (x + h - c) % h = x - c := by
  have hrewrite : x + h - c = h + (x - c) := by omega
  rw [hrewrite, Nat.add_mod_left]
  exact Nat.mod_eq_of_lt (by omega)

theorem phiInvNat_phiNat_of_lt {h x : Nat} (hh : 6 ≤ h) (hx : x < h) :
    phiInvNat h (phiNat h x) = x := by
  unfold phiNat
  by_cases hx3 : x < 3
  · have hx_cases : x = 0 ∨ x = 1 ∨ x = 2 := by omega
    rcases hx_cases with rfl | rfl | rfl
    · have hmod : (0 + h - 3) % h = h - 3 := by
        rw [show 0 + h - 3 = h - 3 by omega]
        exact Nat.mod_eq_of_lt (by omega)
      rw [if_pos (by omega), hmod]
      unfold phiInvNat
      have hnot1 : ¬ (h - 3 + 5 < h) := by omega
      have hnot2 : ¬ (h - 3 + 5 = h) := by omega
      have hnot3 : ¬ (h - 3 + 4 = h) := by omega
      have hyes : h - 3 + 3 = h := by omega
      simp [hnot1, hnot2, hnot3, hyes]
    · have hmod : (1 + h - 3) % h = h - 2 := by
        rw [show 1 + h - 3 = h - 2 by omega]
        exact Nat.mod_eq_of_lt (by omega)
      rw [if_pos (by omega), hmod]
      unfold phiInvNat
      have hnot1 : ¬ (h - 2 + 5 < h) := by omega
      have hnot2 : ¬ (h - 2 + 5 = h) := by omega
      have hnot3 : ¬ (h - 2 + 4 = h) := by omega
      have hnot4 : ¬ (h - 2 + 3 = h) := by omega
      have hyes : h - 2 + 2 = h := by omega
      simp [hnot1, hnot2, hnot3, hnot4, hyes,
        Nat.mod_eq_of_lt (by omega : 1 < h)]
    · have hmod : (2 + h - 3) % h = h - 1 := by
        rw [show 2 + h - 3 = h - 1 by omega]
        exact Nat.mod_eq_of_lt (by omega)
      rw [if_pos (by omega), hmod]
      unfold phiInvNat
      have hnot1 : ¬ (h - 1 + 5 < h) := by omega
      have hnot2 : ¬ (h - 1 + 5 = h) := by omega
      have hnot3 : ¬ (h - 1 + 4 = h) := by omega
      have hnot4 : ¬ (h - 1 + 3 = h) := by omega
      have hnot5 : ¬ (h - 1 + 2 = h) := by omega
      simp [hnot1, hnot2, hnot3, hnot4, hnot5,
        Nat.mod_eq_of_lt (by omega : 2 < h)]
  · by_cases hx5 : x < 5
    · have hx_cases : x = 3 ∨ x = 4 := by omega
      rcases hx_cases with rfl | rfl
      · have hmod : (3 + h - 8) % h = h - 5 := by
          rw [show 3 + h - 8 = h - 5 by omega]
          exact Nat.mod_eq_of_lt (by omega)
        rw [if_neg (by omega), if_pos (by omega), hmod]
        unfold phiInvNat
        have hyes : h - 5 + 5 = h := by omega
        simp [hyes, Nat.mod_eq_of_lt (by omega : 3 < h)]
      · have hmod : (4 + h - 8) % h = h - 4 := by
          rw [show 4 + h - 8 = h - 4 by omega]
          exact Nat.mod_eq_of_lt (by omega)
        rw [if_neg (by omega), if_pos (by omega), hmod]
        unfold phiInvNat
        have hnot1 : ¬ (h - 4 + 5 < h) := by omega
        have hnot2 : ¬ (h - 4 + 5 = h) := by omega
        have hyes : h - 4 + 4 = h := by omega
        simp [hnot1, hnot2, hyes, Nat.mod_eq_of_lt (by omega : 4 < h)]
    · have hxge5 : 5 ≤ x := by omega
      have hmod : (x + h - 5) % h = x - 5 :=
        add_sub_mod_eq_sub hxge5 hx
      rw [if_neg hx3, if_neg hx5, hmod]
      unfold phiInvNat
      have hlt : x - 5 + 5 < h := by omega
      rw [if_pos hlt]
      have hsum : x - 5 + 5 = x := by omega
      rw [hsum]
      exact Nat.mod_eq_of_lt hx

theorem phiInv_phi_of_six_le {h : Nat} [NeZero h] (hh : 6 ≤ h) :
    Function.LeftInverse (phiInv h) (phi h) := by
  intro x
  apply Fin.ext
  exact phiInvNat_phiNat_of_lt hh x.isLt

theorem phiNat_phiInvNat_of_lt {h x : Nat} (hh : 6 ≤ h) (hx : x < h) :
    phiNat h (phiInvNat h x) = x := by
  unfold phiInvNat
  by_cases hlt : x + 5 < h
  · rw [if_pos hlt]
    have hmod : (x + 5) % h = x + 5 := Nat.mod_eq_of_lt hlt
    rw [hmod]
    unfold phiNat
    rw [if_neg (by omega : ¬ x + 5 < 3)]
    rw [if_neg (by omega : ¬ x + 5 < 5)]
    have hsum : x + 5 + h - 5 = h + x := by omega
    rw [hsum, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt hx
  · rw [if_neg hlt]
    by_cases heq5 : x + 5 = h
    · rw [if_pos heq5]
      have hmod3 : 3 % h = 3 := Nat.mod_eq_of_lt (by omega)
      rw [hmod3]
      unfold phiNat
      rw [if_neg (by omega : ¬ 3 < 3)]
      rw [if_pos (by omega : 3 < 5)]
      have hmod : (3 + h - 8) % h = h - 5 := by
        rw [show 3 + h - 8 = h - 5 by omega]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      omega
    · rw [if_neg heq5]
      by_cases heq4 : x + 4 = h
      · rw [if_pos heq4]
        have hmod4 : 4 % h = 4 := Nat.mod_eq_of_lt (by omega)
        rw [hmod4]
        unfold phiNat
        rw [if_neg (by omega : ¬ 4 < 3)]
        rw [if_pos (by omega : 4 < 5)]
        have hmod : (4 + h - 8) % h = h - 4 := by
          rw [show 4 + h - 8 = h - 4 by omega]
          exact Nat.mod_eq_of_lt (by omega)
        rw [hmod]
        omega
      · rw [if_neg heq4]
        by_cases heq3 : x + 3 = h
        · rw [if_pos heq3]
          unfold phiNat
          rw [if_pos (by omega : 0 < 3)]
          have hmod : (0 + h - 3) % h = h - 3 := by
            rw [show 0 + h - 3 = h - 3 by omega]
            exact Nat.mod_eq_of_lt (by omega)
          rw [hmod]
          omega
        · rw [if_neg heq3]
          by_cases heq2 : x + 2 = h
          · rw [if_pos heq2]
            have hmod1 : 1 % h = 1 := Nat.mod_eq_of_lt (by omega)
            rw [hmod1]
            unfold phiNat
            rw [if_pos (by omega : 1 < 3)]
            have hmod : (1 + h - 3) % h = h - 2 := by
              rw [show 1 + h - 3 = h - 2 by omega]
              exact Nat.mod_eq_of_lt (by omega)
            rw [hmod]
            omega
          · rw [if_neg heq2]
            have hxlast : x + 1 = h := by omega
            have hmod2 : 2 % h = 2 := Nat.mod_eq_of_lt (by omega)
            rw [hmod2]
            unfold phiNat
            rw [if_pos (by omega : 2 < 3)]
            have hmod : (2 + h - 3) % h = h - 1 := by
              rw [show 2 + h - 3 = h - 1 by omega]
              exact Nat.mod_eq_of_lt (by omega)
            rw [hmod]
            omega

theorem phi_phiInv_of_six_le {h : Nat} [NeZero h] (hh : 6 ≤ h) :
    Function.RightInverse (phiInv h) (phi h) := by
  intro x
  apply Fin.ext
  exact phiNat_phiInvNat_of_lt hh x.isLt

theorem phi_bijective_of_six_le {h : Nat} [NeZero h] (hh : 6 ≤ h) :
    Function.Bijective (phi h) :=
  bijective_of_inverse (phi h) (phiInv h)
    (phiInv_phi_of_six_le hh) (phi_phiInv_of_six_le hh)

private theorem iterate_left_inverse {α : Type*} {f g : α → α}
    (hright : Function.RightInverse g f) :
    ∀ n x, (f^[n]) ((g^[n]) x) = x := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply]
      rw [Function.iterate_succ_apply']
      rw [hright]
      exact ih x

theorem single_cycle_of_inverse {α : Type*} {f g : α → α}
    (hleft : Function.LeftInverse g f)
    (hright : Function.RightInverse g f)
    (hg : IsSingleCycleMap g) :
    IsSingleCycleMap f := by
  refine ⟨bijective_of_inverse f g hleft hright, ?_⟩
  intro x y
  rcases hg.2 y x with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  calc
    (f^[n]) x = (f^[n]) ((g^[n]) y) := by rw [hn]
    _ = y := iterate_left_inverse hright n y

theorem single_cycle_iff_of_inverse {α : Type*} {f g : α → α}
    (hleft : Function.LeftInverse g f)
    (hright : Function.RightInverse g f) :
    IsSingleCycleMap f ↔ IsSingleCycleMap g := by
  constructor
  · exact single_cycle_of_inverse hright hleft
  · exact single_cycle_of_inverse hleft hright

theorem phi_single_cycle_iff_phiInv {h : Nat} [NeZero h] (hh : 6 ≤ h) :
    IsSingleCycleMap (phi h) ↔ IsSingleCycleMap (phiInv h) :=
  single_cycle_iff_of_inverse
    (phiInv_phi_of_six_le hh) (phi_phiInv_of_six_le hh)

theorem phi_single_cycle_of_phiInv {h : Nat} [NeZero h] (hh : 6 ≤ h)
    (hinv : IsSingleCycleMap (phiInv h)) :
    IsSingleCycleMap (phi h) :=
  (phi_single_cycle_iff_phiInv hh).2 hinv

theorem phiInv_single_cycle_of_phi {h : Nat} [NeZero h] (hh : 6 ≤ h)
    (hphi : IsSingleCycleMap (phi h)) :
    IsSingleCycleMap (phiInv h) :=
  (phi_single_cycle_iff_phiInv hh).1 hphi

theorem phiInvNat_mod_five_of_bad {h x : Nat}
    (hh : 6 ≤ h) (hbad : h % 5 = 3) (hx : x < h) :
    ((phiInvNat h x : Nat) : ZMod 5) = (x : ZMod 5) := by
  rw [phiInvNat_mod_five hh hx]
  by_cases hlt : x + 5 < h
  · simp [hlt]
  · simp [hlt, residueShift_eq_zero_of_bad hbad]

theorem phiInv_iterate_mod_five_of_bad {h : Nat} [NeZero h]
    (hh : 6 ≤ h) (hbad : h % 5 = 3) :
    ∀ n (x : Fin h),
      ((((phiInv h)^[n]) x).val : ZMod 5) = (x.val : ZMod 5) := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      calc
        ((phiInv h (((phiInv h)^[n]) x)).val : ZMod 5) =
            ((((phiInv h)^[n]) x).val : ZMod 5) := by
          exact phiInvNat_mod_five_of_bad hh hbad (((phiInv h)^[n]) x).isLt
        _ = (x.val : ZMod 5) := ih x

theorem phiInv_not_single_cycle_of_bad {h : Nat} [NeZero h]
    (hh : 6 ≤ h) (hbad : h % 5 = 3) :
    ¬ IsSingleCycleMap (phiInv h) := by
  intro hcycle
  let y : Fin h := ⟨1, by omega⟩
  rcases hcycle.2 (0 : Fin h) y with ⟨n, hn⟩
  have hres := phiInv_iterate_mod_five_of_bad hh hbad n (0 : Fin h)
  change ((((phiInv h)^[n]) (0 : Fin h)).val : ZMod 5) =
    (0 : ZMod 5) at hres
  rw [hn] at hres
  change (1 : ZMod 5) = (0 : ZMod 5) at hres
  exact (by decide : (1 : ZMod 5) ≠ 0) hres

theorem phi_not_single_cycle_of_bad {h : Nat} [NeZero h]
    (hh : 6 ≤ h) (hbad : h % 5 = 3) :
    ¬ IsSingleCycleMap (phi h) := by
  intro hcycle
  exact phiInv_not_single_cycle_of_bad hh hbad
    (phiInv_single_cycle_of_phi hh hcycle)

theorem goodPhiClass_of_phi_single_cycle {h : Nat} [NeZero h]
    (hh : 6 ≤ h) (hcycle : IsSingleCycleMap (phi h)) :
    goodPhiClass h := by
  intro hbad
  exact phi_not_single_cycle_of_bad hh hbad hcycle

structure TargetASeamQuotientArithmetic (h : Nat) [NeZero h] : Type where
  hmin : 6 ≤ h
  single_cycle_iff : IsSingleCycleMap (phi h) ↔ goodPhiClass h
  bad_class_five_cycles :
    h % 5 = 3 →
      ∃ C : Finset (Fin h → Prop),
        C.card = 5 ∧
        ∀ x : Fin h, ∃ component ∈ C, component x

theorem TargetASeamQuotientArithmetic.phi_bijective
    {h : Nat} [NeZero h] (pkg : TargetASeamQuotientArithmetic h) :
    Function.Bijective (phi h) :=
  phi_bijective_of_six_le pkg.hmin

structure TargetASeamQuotientPackage (m h : Nat) [NeZero m] [NeZero h] : Type where
  hm : m = 2 * h + 1
  hodd_range : 13 ≤ m
  arithmetic : TargetASeamQuotientArithmetic h
  q_hitting_23 : Prop
  q_hitting_23_proof : q_hitting_23
  q_hitting_32 : Prop
  q_hitting_32_proof : q_hitting_32
  q_first_return_23 : Prop
  q_first_return_23_proof : q_first_return_23
  q_first_return_32 : Prop
  q_first_return_32_proof : q_first_return_32
  length_sum_23 : Prop
  length_sum_23_proof : length_sum_23
  length_sum_32 : Prop
  length_sum_32_proof : length_sum_32

end TargetA
end Handoff
end D7Odd
