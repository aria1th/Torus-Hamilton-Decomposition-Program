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

def Reaches {α : Type*} (f : α → α) (x y : α) : Prop :=
  ∃ n, f^[n] x = y

theorem Reaches.refl {α : Type*} {f : α → α} (x : α) :
    Reaches f x x :=
  ⟨0, by simp⟩

theorem Reaches.trans {α : Type*} {f : α → α} {x y z : α}
    (hxy : Reaches f x y) (hyz : Reaches f y z) :
    Reaches f x z := by
  rcases hxy with ⟨m, hm⟩
  rcases hyz with ⟨n, hn⟩
  refine ⟨n + m, ?_⟩
  rw [Function.iterate_add_apply]
  rw [hm]
  exact hn

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

theorem phiInv_reaches_internal_target_reaches {h : Nat} [NeZero h] {x y : Nat}
    (hxy : x ≤ y) (hmod : (y : ZMod 5) = (x : ZMod 5)) (hy : y < h) :
    Reaches (phiInv h) (⟨x, by omega⟩ : Fin h) (⟨y, hy⟩ : Fin h) :=
  phiInv_reaches_internal_target hxy hmod hy

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

theorem phiInv_reaches_next_low_reaches {h : Nat} [NeZero h] (hh : 6 ≤ h)
    {x b : Nat} (hx : x < h) (hb : b < 5)
    (hbmod : (b : ZMod 5) = (x : ZMod 5) + residueShift h) :
    Reaches (phiInv h) (⟨x, hx⟩ : Fin h) (⟨b, by omega⟩ : Fin h) :=
  phiInv_reaches_next_low hh hx hb hbmod

def zmod5Low (r : ZMod 5) : Nat :=
  r.val

theorem zmod5Low_lt (r : ZMod 5) :
    zmod5Low r < 5 :=
  ZMod.val_lt r

theorem zmod5Low_cast (r : ZMod 5) :
    ((zmod5Low r : Nat) : ZMod 5) = r :=
  ZMod.natCast_zmod_val r

theorem zmod5Low_natCast_le (n : Nat) :
    zmod5Low ((n : Nat) : ZMod 5) ≤ n := by
  unfold zmod5Low
  rw [ZMod.val_natCast]
  exact Nat.mod_le n 5

def zmod5LowFin (h : Nat) [NeZero h] (hh : 6 ≤ h)
    (r : ZMod 5) : Fin h :=
  ⟨zmod5Low r, by
    have hlt := zmod5Low_lt r
    omega⟩

theorem phiInv_reaches_low_step {h : Nat} [NeZero h] (hh : 6 ≤ h)
    (r : ZMod 5) :
    Reaches (phiInv h) (zmod5LowFin h hh r)
      (zmod5LowFin h hh (r + residueShift h)) := by
  have hstep := phiInv_reaches_next_low_reaches (h := h) hh
    (x := zmod5Low r) (b := zmod5Low (r + residueShift h))
    (by
      have hlt := zmod5Low_lt r
      omega)
    (zmod5Low_lt (r + residueShift h))
    (by
      calc
        ((zmod5Low (r + residueShift h) : Nat) : ZMod 5) =
            r + residueShift h := zmod5Low_cast (r + residueShift h)
        _ = ((zmod5Low r : Nat) : ZMod 5) + residueShift h := by
          rw [zmod5Low_cast r])
  simpa [zmod5LowFin] using hstep

theorem phiInv_reaches_low_iter {h : Nat} [NeZero h] (hh : 6 ≤ h) :
    ∀ n r,
      Reaches (phiInv h) (zmod5LowFin h hh r)
        (zmod5LowFin h hh (((fun r : ZMod 5 => r + residueShift h)^[n]) r)) := by
  intro n
  induction n with
  | zero =>
      intro r
      simpa using Reaches.refl (f := phiInv h) (zmod5LowFin h hh r)
  | succ n ih =>
      intro r
      have hfirst := ih r
      have hstep := phiInv_reaches_low_step (h := h) hh
        (((fun r : ZMod 5 => r + residueShift h)^[n]) r)
      exact Reaches.trans hfirst
        (by simpa [Function.iterate_succ_apply'] using hstep)

theorem phiInv_reaches_low_of_residue_reaches
    {h : Nat} [NeZero h] (hh : 6 ≤ h) {r s : ZMod 5}
    (hres : Reaches (fun r : ZMod 5 => r + residueShift h) r s) :
    Reaches (phiInv h) (zmod5LowFin h hh r) (zmod5LowFin h hh s) := by
  rcases hres with ⟨n, hn⟩
  have hiter := phiInv_reaches_low_iter (h := h) hh n r
  simpa [hn] using hiter

theorem phiInv_reaches_any_of_good {h : Nat} [NeZero h]
    (hh : 6 ≤ h) (hgood : goodPhiClass h) (x y : Fin h) :
    Reaches (phiInv h) x y := by
  let r0 : ZMod 5 := (x.val : ZMod 5) + residueShift h
  have hx_to_low :
      Reaches (phiInv h) x (zmod5LowFin h hh r0) := by
    have hstep := phiInv_reaches_next_low_reaches (h := h) hh
      (x := x.val) (b := zmod5Low r0) x.isLt (zmod5Low_lt r0)
      (by
        unfold r0
        exact zmod5Low_cast ((x.val : ZMod 5) + residueShift h))
    simpa [zmod5LowFin] using hstep
  have hquot := residueShift_add_single_cycle_of_good (h := h) hgood
  rcases hquot.2 r0 (y.val : ZMod 5) with ⟨n, hn⟩
  have hlow :
      Reaches (phiInv h) (zmod5LowFin h hh r0)
        (zmod5LowFin h hh (y.val : ZMod 5)) := by
    exact phiInv_reaches_low_of_residue_reaches (h := h) hh ⟨n, hn⟩
  have hfinish :
      Reaches (phiInv h) (zmod5LowFin h hh (y.val : ZMod 5)) y := by
    have hinternal := phiInv_reaches_internal_target_reaches (h := h)
      (x := zmod5Low (y.val : ZMod 5)) (y := y.val)
      (zmod5Low_natCast_le y.val)
      ((zmod5Low_cast (y.val : ZMod 5)).symm)
      y.isLt
    simpa [zmod5LowFin] using hinternal
  exact Reaches.trans hx_to_low (Reaches.trans hlow hfinish)

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

theorem bijective_of_reaches_all {α : Type*} [Finite α]
    (f : α → α) (hreach : ∀ x y : α, ∃ n : Nat, f^[n] x = y) :
    Function.Bijective f := by
  have hsurj : Function.Surjective f := by
    intro y
    rcases hreach (f y) y with ⟨n, hn⟩
    cases n with
    | zero =>
        exact ⟨y, hn⟩
    | succ n =>
        refine ⟨f^[n] (f y), ?_⟩
        simpa [Function.iterate_succ_apply'] using hn
  exact ⟨(Finite.injective_iff_surjective).2 hsurj, hsurj⟩

theorem single_cycle_of_reaches_all {α : Type*} [Finite α]
    (f : α → α) (hreach : ∀ x y : α, ∃ n : Nat, f^[n] x = y) :
    IsSingleCycleMap f :=
  ⟨bijective_of_reaches_all f hreach, hreach⟩

theorem reaches_all_of_return_cover
    {α σ : Type*} (f : α → α) (base : σ → α)
    (next : σ → σ) (time : σ → Nat)
    (hreturn : ∀ s : σ, f^[time s] (base s) = base (next s))
    (hcover : ∀ x : α, ∃ s : σ, ∃ k : Nat,
      k < time s ∧ f^[k] (base s) = x)
    (hnext : IsSingleCycleMap next) :
    ∀ x y : α, ∃ n : Nat, f^[n] x = y := by
  have hbase : ∀ (s : σ) (n : Nat),
      ∃ N : Nat, f^[N] (base s) = base (next^[n] s) := by
    intro s n
    induction n with
    | zero =>
        exact ⟨0, rfl⟩
    | succ n ih =>
        rcases ih with ⟨N, hN⟩
        let u : σ := next^[n] s
        refine ⟨time u + N, ?_⟩
        calc
          f^[time u + N] (base s) = f^[time u] (f^[N] (base s)) := by
            rw [Function.iterate_add_apply]
          _ = f^[time u] (base u) := by rw [hN]
          _ = base (next u) := hreturn u
          _ = base (next^[n.succ] s) := by
            rw [Function.iterate_succ_apply']
  intro x y
  rcases hcover x with ⟨sx, kx, hkx, hx⟩
  rcases hcover y with ⟨sy, ky, _hky, hy⟩
  let A := time sx - kx
  have hfromx : f^[A] x = base (next sx) := by
    rw [← hx]
    change f^[time sx - kx] (f^[kx] (base sx)) = base (next sx)
    rw [← Function.iterate_add_apply]
    rw [Nat.sub_add_cancel (Nat.le_of_lt hkx)]
    exact hreturn sx
  rcases hnext.2 (next sx) sy with ⟨r, hr⟩
  rcases hbase (next sx) r with ⟨N, hN⟩
  have htoSy : f^[N] (base (next sx)) = base sy := by
    rw [hN, hr]
  refine ⟨ky + (N + A), ?_⟩
  calc
    f^[ky + (N + A)] x = f^[ky] (f^[N + A] x) := by
      rw [Function.iterate_add_apply]
    _ = f^[ky] (base sy) := by
      congr
      calc
        f^[N + A] x = f^[N] (f^[A] x) := by
          rw [Function.iterate_add_apply]
        _ = f^[N] (base (next sx)) := by rw [hfromx]
        _ = base sy := htoSy
    _ = y := hy

theorem single_cycle_of_return_cover_finite
    {α σ : Type*} [Finite α] (f : α → α) (base : σ → α)
    (next : σ → σ) (time : σ → Nat)
    (hreturn : ∀ s : σ, f^[time s] (base s) = base (next s))
    (hcover : ∀ x : α, ∃ s : σ, ∃ k : Nat,
      k < time s ∧ f^[k] (base s) = x)
    (hnext : IsSingleCycleMap next) :
    IsSingleCycleMap f :=
  single_cycle_of_reaches_all f
    (reaches_all_of_return_cover f base next time hreturn hcover hnext)

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

theorem phiInv_single_cycle_of_good {h : Nat} [NeZero h]
    (hh : 6 ≤ h) (hgood : goodPhiClass h) :
    IsSingleCycleMap (phiInv h) := by
  refine ⟨?_, ?_⟩
  · exact bijective_of_inverse (phiInv h) (phi h)
      (phi_phiInv_of_six_le hh) (phiInv_phi_of_six_le hh)
  · intro x y
    exact phiInv_reaches_any_of_good hh hgood x y

theorem phi_single_cycle_of_good {h : Nat} [NeZero h]
    (hh : 6 ≤ h) (hgood : goodPhiClass h) :
    IsSingleCycleMap (phi h) :=
  phi_single_cycle_of_phiInv hh (phiInv_single_cycle_of_good hh hgood)

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

theorem phi_single_cycle_iff_goodPhiClass {h : Nat} [NeZero h]
    (hh : 6 ≤ h) :
    IsSingleCycleMap (phi h) ↔ goodPhiClass h := by
  constructor
  · exact goodPhiClass_of_phi_single_cycle hh
  · exact phi_single_cycle_of_good hh

theorem residueComponentCover {h : Nat} [NeZero h] (hh : 6 ≤ h) :
    ∃ C : Finset (Fin h → Prop),
      C.card = 5 ∧ ∀ x : Fin h, ∃ component ∈ C, component x := by
  classical
  let component : ZMod 5 → Fin h → Prop :=
    fun r x => (x.val : ZMod 5) = r
  refine ⟨Finset.univ.image component, ?_, ?_⟩
  · rw [Finset.card_image_of_injective]
    · simp [ZMod.card]
    · intro r s hrs
      have hr : component r (zmod5LowFin h hh r) := by
        simp [component, zmod5LowFin, zmod5Low_cast r]
      have hs : component s (zmod5LowFin h hh r) := by
        simpa [hrs] using hr
      dsimp [component, zmod5LowFin] at hs
      calc
        r = ((zmod5Low r : Nat) : ZMod 5) := (zmod5Low_cast r).symm
        _ = s := hs
  · intro x
    refine ⟨component (x.val : ZMod 5), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(x.val : ZMod 5), Finset.mem_univ _, rfl⟩
    · simp [component]

theorem badClassFiveCycles_of_six_le {h : Nat} [NeZero h]
    (hh : 6 ≤ h) (_hbad : h % 5 = 3) :
    ∃ C : Finset (Fin h → Prop),
      C.card = 5 ∧ ∀ x : Fin h, ∃ component ∈ C, component x :=
  residueComponentCover hh

structure TargetASeamQuotientArithmetic (h : Nat) [NeZero h] : Type where
  hmin : 6 ≤ h
  single_cycle_iff : IsSingleCycleMap (phi h) ↔ goodPhiClass h
  bad_class_five_cycles :
    h % 5 = 3 →
      ∃ C : Finset (Fin h → Prop),
        C.card = 5 ∧
        ∀ x : Fin h, ∃ component ∈ C, component x

def TargetASeamQuotientArithmetic.ofBadClassComponents
    {h : Nat} [NeZero h] (hh : 6 ≤ h)
    (hbad :
      h % 5 = 3 →
        ∃ C : Finset (Fin h → Prop),
          C.card = 5 ∧
          ∀ x : Fin h, ∃ component ∈ C, component x) :
    TargetASeamQuotientArithmetic h where
  hmin := hh
  single_cycle_iff := phi_single_cycle_iff_goodPhiClass hh
  bad_class_five_cycles := hbad

def TargetASeamQuotientArithmetic.ofSixLe
    {h : Nat} [NeZero h] (hh : 6 ≤ h) :
    TargetASeamQuotientArithmetic h :=
  TargetASeamQuotientArithmetic.ofBadClassComponents hh
    (badClassFiveCycles_of_six_le hh)

theorem TargetASeamQuotientArithmetic.phi_bijective
    {h : Nat} [NeZero h] (pkg : TargetASeamQuotientArithmetic h) :
    Function.Bijective (phi h) :=
  phi_bijective_of_six_le pkg.hmin

inductive QKind where
  | B
  | A
deriving DecidableEq, Repr, Fintype

structure QRawLabel where
  kind : QKind
  value : Nat
deriving DecidableEq, Repr

namespace QRawLabel

def valid (m : Nat) (label : QRawLabel) : Prop :=
  1 ≤ label.value ∧ label.value < m

def B (value : Nat) : QRawLabel :=
  ⟨QKind.B, value⟩

def A (value : Nat) : QRawLabel :=
  ⟨QKind.A, value⟩

end QRawLabel

def targetARep1ToH (h value : Nat) : Nat :=
  ((value - 1) % h) + 1

def targetAPhiOne (h x : Nat) : Nat :=
  phiNat h (x - 1) + 1

def targetATau23One (h x : Nat) : Nat :=
  if x ≤ 3 then
    targetARep1ToH h (x + h - 4)
  else if x ≤ 5 then
    targetARep1ToH h (x + h - 9)
  else if x = 6 then
    targetARep1ToH h (x + h - 6)
  else
    x - 6

def targetAQExpectedB (m : Nat) (value : Nat) : QRawLabel :=
  if value + 1 < m then
    QRawLabel.B (value + 1)
  else
    QRawLabel.A 1

def targetAQExpected23 (m h : Nat) (label : QRawLabel) : QRawLabel :=
  match label.kind with
  | QKind.B => targetAQExpectedB m label.value
  | QKind.A =>
      if label.value % 2 = 0 then
        let x := label.value / 2
        if x ≤ h - 1 then
          QRawLabel.A (2 * x + 1)
        else
          QRawLabel.B 1
      else
        let x := (label.value + 1) / 2
        QRawLabel.A (2 * targetATau23One h x)

def targetAQExpected32 (m h : Nat) (label : QRawLabel) : QRawLabel :=
  match label.kind with
  | QKind.B => targetAQExpectedB m label.value
  | QKind.A =>
      if label.value % 2 = 1 then
        let x := (label.value + 1) / 2
        QRawLabel.A (2 * x)
      else
        let x := label.value / 2
        if x = 6 then
          QRawLabel.B 1
        else
          QRawLabel.A (2 * targetAPhiOne h x - 1)

def targetAQFirstReturnFormula
    (m : Nat) (expected actual : QRawLabel → QRawLabel) : Prop :=
  ∀ label, label.valid m → actual label = expected label

def targetAQFirstReturn23Formula
    (m h : Nat) (actual : QRawLabel → QRawLabel) : Prop :=
  targetAQFirstReturnFormula m (targetAQExpected23 m h) actual

def targetAQFirstReturn32Formula
    (m h : Nat) (actual : QRawLabel → QRawLabel) : Prop :=
  targetAQFirstReturnFormula m (targetAQExpected32 m h) actual

theorem targetAQExpectedB_step {m value : Nat}
    (hstep : value + 1 < m) :
    targetAQExpectedB m value = QRawLabel.B (value + 1) := by
  simp [targetAQExpectedB, hstep]

theorem targetAQExpectedB_wrap {m value : Nat}
    (hwrap : ¬ value + 1 < m) :
    targetAQExpectedB m value = QRawLabel.A 1 := by
  simp [targetAQExpectedB, hwrap]

theorem targetAQExpected23_B_step {m h value : Nat}
    (hstep : value + 1 < m) :
    targetAQExpected23 m h (QRawLabel.B value) =
      QRawLabel.B (value + 1) := by
  simp [targetAQExpected23, targetAQExpectedB_step hstep, QRawLabel.B]

theorem targetAQExpected23_B_wrap {m h value : Nat}
    (hwrap : ¬ value + 1 < m) :
    targetAQExpected23 m h (QRawLabel.B value) = QRawLabel.A 1 := by
  simp [targetAQExpected23, targetAQExpectedB_wrap hwrap, QRawLabel.B]

theorem targetAQExpected32_B_step {m h value : Nat}
    (hstep : value + 1 < m) :
    targetAQExpected32 m h (QRawLabel.B value) =
      QRawLabel.B (value + 1) := by
  simp [targetAQExpected32, targetAQExpectedB_step hstep, QRawLabel.B]

theorem targetAQExpected32_B_wrap {m h value : Nat}
    (hwrap : ¬ value + 1 < m) :
    targetAQExpected32 m h (QRawLabel.B value) = QRawLabel.A 1 := by
  simp [targetAQExpected32, targetAQExpectedB_wrap hwrap, QRawLabel.B]

theorem targetAQExpected23_A_even_step {m h x : Nat}
    (hx : x ≤ h - 1) :
    targetAQExpected23 m h (QRawLabel.A (2 * x)) =
      QRawLabel.A (2 * x + 1) := by
  simp [targetAQExpected23, QRawLabel.A, hx]

theorem targetAQExpected23_A_even_wrap {m h x : Nat}
    (hx : ¬ x ≤ h - 1) :
    targetAQExpected23 m h (QRawLabel.A (2 * x)) = QRawLabel.B 1 := by
  simp [targetAQExpected23, QRawLabel.A, hx]

theorem targetAQExpected23_A_odd_step {m h x : Nat} :
    targetAQExpected23 m h (QRawLabel.A (2 * x + 1)) =
      QRawLabel.A (2 * targetATau23One h (x + 1)) := by
  have hdiv : (2 * x + 1 + 1) / 2 = x + 1 := by
    rw [show 2 * x + 1 + 1 = 2 * (x + 1) by omega]
    exact Nat.mul_div_right (x + 1) (by decide : 0 < 2)
  simp [targetAQExpected23, QRawLabel.A, hdiv]

theorem targetAQExpected32_A_odd_step {m h x : Nat} :
    targetAQExpected32 m h (QRawLabel.A (2 * x + 1)) =
      QRawLabel.A (2 * (x + 1)) := by
  have hdiv : (2 * x + 1 + 1) / 2 = x + 1 := by
    rw [show 2 * x + 1 + 1 = 2 * (x + 1) by omega]
    exact Nat.mul_div_right (x + 1) (by decide : 0 < 2)
  simp [targetAQExpected32, QRawLabel.A, hdiv]

theorem targetAQExpected32_A_even_wrap {m h : Nat} :
    targetAQExpected32 m h (QRawLabel.A 12) = QRawLabel.B 1 := by
  simp [targetAQExpected32, QRawLabel.A]

theorem targetAQExpected32_A_even_step {m h x : Nat}
    (hx : x ≠ 6) :
    targetAQExpected32 m h (QRawLabel.A (2 * x)) =
      QRawLabel.A (2 * targetAPhiOne h x - 1) := by
  simp [targetAQExpected32, QRawLabel.A, hx]

theorem targetAQExpected23_A_odd_two_step {m h x : Nat}
    (htau : targetATau23One h (x + 1) ≤ h - 1) :
    (targetAQExpected23 m h)^[2] (QRawLabel.A (2 * x + 1)) =
      QRawLabel.A (2 * targetATau23One h (x + 1) + 1) := by
  rw [show 2 = 1 + 1 by rfl]
  rw [Function.iterate_add_apply]
  simp [targetAQExpected23_A_odd_step,
    targetAQExpected23_A_even_step (m := m) (h := h) htau]

theorem targetAQExpected23_A_odd_two_step_wrap {m h x : Nat}
    (htau : ¬ targetATau23One h (x + 1) ≤ h - 1) :
    (targetAQExpected23 m h)^[2] (QRawLabel.A (2 * x + 1)) =
      QRawLabel.B 1 := by
  rw [show 2 = 1 + 1 by rfl]
  rw [Function.iterate_add_apply]
  simp [targetAQExpected23_A_odd_step,
    targetAQExpected23_A_even_wrap (m := m) (h := h) htau]

theorem targetAQExpected32_A_odd_two_step {m h x : Nat}
    (hx : x + 1 ≠ 6) :
    (targetAQExpected32 m h)^[2] (QRawLabel.A (2 * x + 1)) =
      QRawLabel.A (2 * targetAPhiOne h (x + 1) - 1) := by
  rw [show 2 = 1 + 1 by rfl]
  rw [Function.iterate_add_apply]
  simp [targetAQExpected32_A_odd_step,
    targetAQExpected32_A_even_step (m := m) (h := h) hx]

theorem targetAQExpected32_A_odd_two_step_wrap {m h : Nat} :
    (targetAQExpected32 m h)^[2] (QRawLabel.A 11) = QRawLabel.B 1 := by
  rw [show 2 = 1 + 1 by rfl]
  rw [Function.iterate_add_apply]
  change targetAQExpected32 m h
      (targetAQExpected32 m h (QRawLabel.A (2 * 5 + 1))) = QRawLabel.B 1
  rw [targetAQExpected32_A_odd_step (m := m) (h := h) (x := 5)]
  exact targetAQExpected32_A_even_wrap (m := m) (h := h)

theorem targetAQExpected23_B_iter {m h value n : Nat}
    (hbound : value + n < m) :
    (targetAQExpected23 m h)^[n] (QRawLabel.B value) =
      QRawLabel.B (value + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hprev : value + n < m := by omega
      rw [ih hprev]
      have hstep : value + n + 1 < m := by omega
      simpa [Nat.add_assoc] using
        targetAQExpected23_B_step (m := m) (h := h)
          (value := value + n) hstep

theorem targetAQExpected32_B_iter {m h value n : Nat}
    (hbound : value + n < m) :
    (targetAQExpected32 m h)^[n] (QRawLabel.B value) =
      QRawLabel.B (value + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hprev : value + n < m := by omega
      rw [ih hprev]
      have hstep : value + n + 1 < m := by omega
      simpa [Nat.add_assoc] using
        targetAQExpected32_B_step (m := m) (h := h)
          (value := value + n) hstep

theorem targetAQExpected23_B_one_to_A_one {m h : Nat}
    (hm : 1 < m) :
    (targetAQExpected23 m h)^[m - 1] (QRawLabel.B 1) = QRawLabel.A 1 := by
  rw [show m - 1 = 1 + (m - 2) by omega]
  rw [Function.iterate_add_apply]
  rw [targetAQExpected23_B_iter (m := m) (h := h) (value := 1)
    (n := m - 2) (by omega)]
  rw [show 1 + (m - 2) = m - 1 by omega]
  have hwrap : ¬ m - 1 + 1 < m := by omega
  simpa using targetAQExpected23_B_wrap (m := m) (h := h)
    (value := m - 1) hwrap

theorem targetAQExpected32_B_one_to_A_one {m h : Nat}
    (hm : 1 < m) :
    (targetAQExpected32 m h)^[m - 1] (QRawLabel.B 1) = QRawLabel.A 1 := by
  rw [show m - 1 = 1 + (m - 2) by omega]
  rw [Function.iterate_add_apply]
  rw [targetAQExpected32_B_iter (m := m) (h := h) (value := 1)
    (n := m - 2) (by omega)]
  rw [show 1 + (m - 2) = m - 1 by omega]
  have hwrap : ¬ m - 1 + 1 < m := by omega
  simpa using targetAQExpected32_B_wrap (m := m) (h := h)
    (value := m - 1) hwrap

theorem targetAQExpected32_A_six_excursion {m h : Nat}
    (hm : m = 2 * h + 1) (hh : 0 < h) :
    (targetAQExpected32 m h)^[2 * h + 2] (QRawLabel.A 11) =
      QRawLabel.A 1 := by
  have hmgt : 1 < m := by omega
  rw [show 2 * h + 2 = (m - 1) + 2 by omega]
  rw [Function.iterate_add_apply]
  rw [targetAQExpected32_A_odd_two_step_wrap]
  exact targetAQExpected32_B_one_to_A_one (m := m) (h := h) hmgt

theorem targetAQExpected32_A_six_to_B_iter {m h n : Nat}
    (hn : 1 + n < m) :
    (targetAQExpected32 m h)^[2 + n] (QRawLabel.A 11) =
      QRawLabel.B (1 + n) := by
  rw [show 2 + n = n + 2 by omega]
  rw [Function.iterate_add_apply]
  rw [targetAQExpected32_A_odd_two_step_wrap]
  exact targetAQExpected32_B_iter (m := m) (h := h) (value := 1)
    (n := n) hn

def targetAQOddA {h : Nat} (x : Fin h) : QRawLabel :=
  QRawLabel.A (2 * x.val + 1)

theorem targetAQOddA_valid {m h : Nat}
    (hm : m = 2 * h + 1) (x : Fin h) :
    (targetAQOddA x).valid m := by
  subst m
  have hxlt : x.val < h := x.isLt
  change 1 ≤ 2 * x.val + 1 ∧ 2 * x.val + 1 < 2 * h + 1
  omega

theorem targetAQExpected32_oddA_to_even {m h : Nat} (x : Fin h) :
    targetAQExpected32 m h (targetAQOddA x) =
      QRawLabel.A (2 * (x.val + 1)) := by
  unfold targetAQOddA
  exact targetAQExpected32_A_odd_step (m := m) (h := h) (x := x.val)

def targetAQExpected32OddATime (h : Nat) (x : Fin h) : Nat :=
  if x.val = 5 then 2 * h + 2 else 2

theorem targetAQExpected32OddATime_pos {h : Nat} (x : Fin h) :
    0 < targetAQExpected32OddATime h x := by
  unfold targetAQExpected32OddATime
  split <;> omega

theorem one_lt_targetAQExpected32OddATime {h : Nat} (x : Fin h) :
    1 < targetAQExpected32OddATime h x := by
  unfold targetAQExpected32OddATime
  split
  · have hxlt : x.val < h := x.isLt
    omega
  · omega

theorem targetAQExpected32_oddA_zero_step {m h : Nat} (x : Fin h) :
    (targetAQExpected32 m h)^[0] (targetAQOddA x) = targetAQOddA x := by
  rfl

theorem targetAQExpected32_oddA_one_step {m h : Nat} (x : Fin h) :
    (targetAQExpected32 m h)^[1] (targetAQOddA x) =
      QRawLabel.A (2 * (x.val + 1)) := by
  simp [targetAQExpected32_oddA_to_even]

theorem targetAQExpected32_oddA_five_to_B_iter
    {m h n : Nat} (hh : 6 ≤ h) (hn : 1 + n < m) :
    (targetAQExpected32 m h)^[2 + n]
        (targetAQOddA (⟨5, by omega⟩ : Fin h)) =
      QRawLabel.B (1 + n) := by
  unfold targetAQOddA
  change (targetAQExpected32 m h)^[2 + n] (QRawLabel.A 11) =
    QRawLabel.B (1 + n)
  exact targetAQExpected32_A_six_to_B_iter (m := m) (h := h) hn

theorem targetAQExpected32_oddA_covers_oddA {m h : Nat} (x : Fin h) :
    ∃ k : Nat,
      k < targetAQExpected32OddATime h x ∧
        (targetAQExpected32 m h)^[k] (targetAQOddA x) =
          targetAQOddA x := by
  exact ⟨0, targetAQExpected32OddATime_pos x, rfl⟩

theorem targetAQExpected32_oddA_covers_evenA {m h : Nat} (x : Fin h) :
    ∃ k : Nat,
      k < targetAQExpected32OddATime h x ∧
        (targetAQExpected32 m h)^[k] (targetAQOddA x) =
          QRawLabel.A (2 * (x.val + 1)) := by
  exact ⟨1, one_lt_targetAQExpected32OddATime x,
    targetAQExpected32_oddA_one_step x⟩

theorem targetAQExpected32_oddA_five_covers_B
    {m h value : Nat} (hm : m = 2 * h + 1) (hh : 6 ≤ h)
    (hv1 : 1 ≤ value) (hvm : value < m) :
    ∃ k : Nat,
      k < targetAQExpected32OddATime h (⟨5, by omega⟩ : Fin h) ∧
        (targetAQExpected32 m h)^[k]
          (targetAQOddA (⟨5, by omega⟩ : Fin h)) =
          QRawLabel.B value := by
  refine ⟨2 + (value - 1), ?_, ?_⟩
  · subst m
    simp [targetAQExpected32OddATime]
    omega
  · have hn : 1 + (value - 1) < m := by omega
    have hcover := targetAQExpected32_oddA_five_to_B_iter
      (m := m) (h := h) (n := value - 1) hh hn
    rw [show 1 + (value - 1) = value by omega] at hcover
    exact hcover

theorem targetAQExpected32_oddA_cover
    {m h : Nat} (hm : m = 2 * h + 1) (hh : 6 ≤ h)
    (label : QRawLabel) (hv : label.valid m) :
    ∃ x : Fin h, ∃ k : Nat,
      k < targetAQExpected32OddATime h x ∧
        (targetAQExpected32 m h)^[k] (targetAQOddA x) = label := by
  subst m
  rcases label with ⟨kind, value⟩
  cases kind
  · rcases hv with ⟨hv1, hvm⟩
    refine ⟨⟨5, by omega⟩, ?_⟩
    exact targetAQExpected32_oddA_five_covers_B
      (m := 2 * h + 1) (h := h) rfl hh hv1 hvm
  · rcases hv with ⟨hv1, hvm⟩
    change 1 ≤ value at hv1
    change value < 2 * h + 1 at hvm
    by_cases hodd : value % 2 = 1
    · have hdecomp : value = 2 * (value / 2) + 1 := by
        have hmoddiv := Nat.mod_add_div value 2
        omega
      let x : Fin h := ⟨value / 2, by omega⟩
      refine ⟨x, ?_⟩
      rcases targetAQExpected32_oddA_covers_oddA (m := 2 * h + 1)
          (h := h) x with ⟨k, hk, heq⟩
      refine ⟨k, hk, ?_⟩
      rw [heq]
      unfold targetAQOddA
      change QRawLabel.A (2 * (value / 2) + 1) = QRawLabel.A value
      exact congrArg QRawLabel.A hdecomp.symm
    · have heven : value % 2 = 0 := by
        have hlt := Nat.mod_lt value (by decide : 0 < 2)
        omega
      have hdecomp : value = 2 * (value / 2) := by
        have hmoddiv := Nat.mod_add_div value 2
        omega
      have hhalf_pos : 1 ≤ value / 2 := by omega
      let x : Fin h := ⟨value / 2 - 1, by omega⟩
      refine ⟨x, ?_⟩
      rcases targetAQExpected32_oddA_covers_evenA (m := 2 * h + 1)
          (h := h) x with ⟨k, hk, heq⟩
      refine ⟨k, hk, ?_⟩
      rw [heq]
      unfold x
      change QRawLabel.A (2 * (value / 2 - 1 + 1)) = QRawLabel.A value
      congr
      omega

theorem targetATau23One_succ_eq_phi_val_of_ne_five
    {h : Nat} [NeZero h] (hh : 6 ≤ h) (x : Fin h)
    (hx : x.val ≠ 5) :
    targetATau23One h (x.val + 1) = (phi h x).val := by
  unfold targetATau23One targetARep1ToH phi phiNat
  by_cases hx2 : x.val ≤ 2
  · have hy3 : x.val + 1 ≤ 3 := by omega
    have hxlt3 : x.val < 3 := by omega
    have hrepr :
        ((x.val + 1 + h - 4 - 1) % h) + 1 = x.val + h - 3 := by
      have hval : x.val + 1 + h - 4 - 1 = x.val + h - 4 := by omega
      rw [hval]
      have hlt : x.val + h - 4 < h := by omega
      have hpos : 1 ≤ x.val + h - 3 := by omega
      rw [Nat.mod_eq_of_lt hlt]
      omega
    have hphi : (x.val + h - 3) % h = x.val + h - 3 := by
      apply Nat.mod_eq_of_lt
      omega
    simp [hy3, hxlt3, hrepr, hphi]
  · by_cases hx4 : x.val ≤ 4
    · have hnot3 : ¬ x.val + 1 ≤ 3 := by omega
      have hy5 : x.val + 1 ≤ 5 := by omega
      have hxlt3 : ¬ x.val < 3 := by omega
      have hxlt5 : x.val < 5 := by omega
      have hrepr :
          ((x.val + 1 + h - 9 - 1) % h) + 1 = x.val + h - 8 := by
        have hval : x.val + 1 + h - 9 - 1 = x.val + h - 9 := by omega
        rw [hval]
        have hlt : x.val + h - 9 < h := by omega
        rw [Nat.mod_eq_of_lt hlt]
        omega
      have hphi : (x.val + h - 8) % h = x.val + h - 8 := by
        apply Nat.mod_eq_of_lt
        omega
      simp [hnot3, hy5, hxlt3, hxlt5, hrepr, hphi]
    · have hnot3 : ¬ x.val + 1 ≤ 3 := by omega
      have hnot5 : ¬ x.val + 1 ≤ 5 := by omega
      have hnot6 : x.val + 1 ≠ 6 := by omega
      have hxlt3 : ¬ x.val < 3 := by omega
      have hxlt5 : ¬ x.val < 5 := by omega
      have hphi : (x.val + h - 5) % h = x.val - 5 := by
        rw [show x.val + h - 5 = h + (x.val - 5) by omega]
        rw [Nat.add_mod_left]
        apply Nat.mod_eq_of_lt
        omega
      simp [hnot3, hnot5, hnot6, hxlt3, hxlt5, hphi]

theorem targetATau23One_succ_eq_h_of_five
    {h : Nat} [NeZero h] (hh : 6 ≤ h) (x : Fin h)
    (hx : x.val = 5) :
    targetATau23One h (x.val + 1) = h := by
  unfold targetATau23One targetARep1ToH
  have hy3 : ¬ x.val + 1 ≤ 3 := by omega
  have hy5 : ¬ x.val + 1 ≤ 5 := by omega
  have hy6 : x.val + 1 = 6 := by omega
  simp [hx]
  omega

def targetAQExpected23OddATime (h : Nat) (x : Fin h) : Nat :=
  if x.val = 5 then 2 * h + 2 else 2

theorem targetAQExpected23OddATime_pos {h : Nat} (x : Fin h) :
    0 < targetAQExpected23OddATime h x := by
  unfold targetAQExpected23OddATime
  split <;> omega

theorem one_lt_targetAQExpected23OddATime {h : Nat} (x : Fin h) :
    1 < targetAQExpected23OddATime h x := by
  unfold targetAQExpected23OddATime
  split
  · have hxlt : x.val < h := x.isLt
    omega
  · omega

theorem phi_val_five {h : Nat} [NeZero h]
    (x : Fin h) (hx : x.val = 5) :
    (phi h x).val = 0 := by
  simp [phi, phiNat, hx, Nat.mod_self]

theorem targetAQExpected23_A_five_excursion {m h : Nat} [NeZero h]
    (hm : m = 2 * h + 1) (hh : 6 ≤ h) :
    (targetAQExpected23 m h)^[2 * h + 2] (QRawLabel.A 11) =
      QRawLabel.A 1 := by
  have hmgt : 1 < m := by omega
  rw [show 2 * h + 2 = (m - 1) + 2 by omega]
  rw [Function.iterate_add_apply]
  have htau : ¬ targetATau23One h (5 + 1) ≤ h - 1 := by
    have ht := targetATau23One_succ_eq_h_of_five hh
      (⟨5, by omega⟩ : Fin h) rfl
    intro hle
    rw [ht] at hle
    omega
  rw [targetAQExpected23_A_odd_two_step_wrap (m := m) (h := h)
    (x := 5) htau]
  exact targetAQExpected23_B_one_to_A_one (m := m) (h := h) hmgt

theorem targetAQExpected23_oddA_return
    {m h : Nat} [NeZero h] (hm : m = 2 * h + 1) (hh : 6 ≤ h)
    (x : Fin h) :
    (targetAQExpected23 m h)^[targetAQExpected23OddATime h x]
        (targetAQOddA x) =
      targetAQOddA (phi h x) := by
  unfold targetAQExpected23OddATime targetAQOddA
  by_cases hx : x.val = 5
  · rw [if_pos hx]
    rw [show 2 * x.val + 1 = 11 by omega]
    rw [targetAQExpected23_A_five_excursion (m := m) (h := h) hm hh]
    have hphi := phi_val_five x hx
    simp [hphi]
  · rw [if_neg hx]
    have htau := targetATau23One_succ_eq_phi_val_of_ne_five hh x hx
    have htau_le : targetATau23One h (x.val + 1) ≤ h - 1 := by
      rw [htau]
      exact Nat.le_pred_of_lt (phi h x).isLt
    rw [targetAQExpected23_A_odd_two_step (m := m) (h := h)
      (x := x.val) htau_le]
    rw [htau]

theorem targetAQExpected23_oddA_to_even {m h : Nat} (x : Fin h) :
    targetAQExpected23 m h (targetAQOddA x) =
      QRawLabel.A (2 * targetATau23One h (x.val + 1)) := by
  unfold targetAQOddA
  exact targetAQExpected23_A_odd_step (m := m) (h := h) (x := x.val)

theorem targetAQExpected23_oddA_one_step {m h : Nat} (x : Fin h) :
    (targetAQExpected23 m h)^[1] (targetAQOddA x) =
      QRawLabel.A (2 * targetATau23One h (x.val + 1)) := by
  simp [targetAQExpected23_oddA_to_even]

theorem targetATau23One_succ_surjective
    {h y : Nat} [NeZero h] (hh : 6 ≤ h)
    (hy1 : 1 ≤ y) (hyh : y ≤ h) :
    ∃ x : Fin h, targetATau23One h (x.val + 1) = y := by
  by_cases htop : y = h
  · subst y
    refine ⟨⟨5, by omega⟩, ?_⟩
    exact targetATau23One_succ_eq_h_of_five hh
      (⟨5, by omega⟩ : Fin h) rfl
  · have hylt : y < h := by omega
    rcases (phi_bijective_of_six_le hh).2 (⟨y, hylt⟩ : Fin h) with
      ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have hval : (phi h x).val = y := by
      exact congrArg Fin.val hx
    have hxne : x.val ≠ 5 := by
      intro hx5
      have hphi := phi_val_five x hx5
      omega
    rw [targetATau23One_succ_eq_phi_val_of_ne_five hh x hxne]
    exact hval

theorem targetAQExpected23_oddA_covers_oddA {m h : Nat} (x : Fin h) :
    ∃ k : Nat,
      k < targetAQExpected23OddATime h x ∧
        (targetAQExpected23 m h)^[k] (targetAQOddA x) =
          targetAQOddA x := by
  exact ⟨0, targetAQExpected23OddATime_pos x, rfl⟩

theorem targetAQExpected23_oddA_covers_evenA
    {m h y : Nat} [NeZero h] (hh : 6 ≤ h)
    (hy1 : 1 ≤ y) (hyh : y ≤ h) :
    ∃ x : Fin h, ∃ k : Nat,
      k < targetAQExpected23OddATime h x ∧
        (targetAQExpected23 m h)^[k] (targetAQOddA x) =
          QRawLabel.A (2 * y) := by
  rcases targetATau23One_succ_surjective hh hy1 hyh with ⟨x, hx⟩
  refine ⟨x, 1, one_lt_targetAQExpected23OddATime x, ?_⟩
  rw [targetAQExpected23_oddA_one_step (m := m) (h := h) x]
  rw [hx]

theorem targetAQExpected23_oddA_five_to_B_iter
    {m h n : Nat} [NeZero h] (hh : 6 ≤ h) (hn : 1 + n < m) :
    (targetAQExpected23 m h)^[2 + n]
        (targetAQOddA (⟨5, by omega⟩ : Fin h)) =
      QRawLabel.B (1 + n) := by
  unfold targetAQOddA
  change (targetAQExpected23 m h)^[2 + n] (QRawLabel.A 11) =
    QRawLabel.B (1 + n)
  rw [show 2 + n = n + 2 by omega]
  rw [Function.iterate_add_apply]
  have htau : ¬ targetATau23One h (5 + 1) ≤ h - 1 := by
    have ht := targetATau23One_succ_eq_h_of_five hh
      (⟨5, by omega⟩ : Fin h) rfl
    intro hle
    rw [ht] at hle
    omega
  rw [targetAQExpected23_A_odd_two_step_wrap (m := m) (h := h)
    (x := 5) htau]
  exact targetAQExpected23_B_iter (m := m) (h := h) (value := 1)
    (n := n) hn

theorem targetAQExpected23_oddA_five_covers_B
    {m h value : Nat} [NeZero h] (hm : m = 2 * h + 1) (hh : 6 ≤ h)
    (hv1 : 1 ≤ value) (hvm : value < m) :
    ∃ k : Nat,
      k < targetAQExpected23OddATime h (⟨5, by omega⟩ : Fin h) ∧
        (targetAQExpected23 m h)^[k]
          (targetAQOddA (⟨5, by omega⟩ : Fin h)) =
          QRawLabel.B value := by
  refine ⟨2 + (value - 1), ?_, ?_⟩
  · subst m
    simp [targetAQExpected23OddATime]
    omega
  · have hn : 1 + (value - 1) < m := by omega
    have hcover := targetAQExpected23_oddA_five_to_B_iter
      (m := m) (h := h) (n := value - 1) hh hn
    rw [show 1 + (value - 1) = value by omega] at hcover
    exact hcover

theorem targetAQExpected23_oddA_cover
    {m h : Nat} [NeZero h] (hm : m = 2 * h + 1) (hh : 6 ≤ h)
    (label : QRawLabel) (hv : label.valid m) :
    ∃ x : Fin h, ∃ k : Nat,
      k < targetAQExpected23OddATime h x ∧
        (targetAQExpected23 m h)^[k] (targetAQOddA x) = label := by
  subst m
  rcases label with ⟨kind, value⟩
  cases kind
  · rcases hv with ⟨hv1, hvm⟩
    refine ⟨⟨5, by omega⟩, ?_⟩
    exact targetAQExpected23_oddA_five_covers_B
      (m := 2 * h + 1) (h := h) rfl hh hv1 hvm
  · rcases hv with ⟨hv1, hvm⟩
    change 1 ≤ value at hv1
    change value < 2 * h + 1 at hvm
    by_cases hodd : value % 2 = 1
    · have hdecomp : value = 2 * (value / 2) + 1 := by
        have hmoddiv := Nat.mod_add_div value 2
        omega
      let x : Fin h := ⟨value / 2, by omega⟩
      refine ⟨x, ?_⟩
      rcases targetAQExpected23_oddA_covers_oddA (m := 2 * h + 1)
          (h := h) x with ⟨k, hk, heq⟩
      refine ⟨k, hk, ?_⟩
      rw [heq]
      unfold targetAQOddA
      change QRawLabel.A (2 * (value / 2) + 1) = QRawLabel.A value
      exact congrArg QRawLabel.A hdecomp.symm
    · have heven : value % 2 = 0 := by
        have hlt := Nat.mod_lt value (by decide : 0 < 2)
        omega
      have hdecomp : value = 2 * (value / 2) := by
        have hmoddiv := Nat.mod_add_div value 2
        omega
      have hhalf_pos : 1 ≤ value / 2 := by omega
      have hhalf_le : value / 2 ≤ h := by omega
      rcases targetAQExpected23_oddA_covers_evenA (m := 2 * h + 1)
          (h := h) hh hhalf_pos hhalf_le with ⟨x, k, hk, heq⟩
      refine ⟨x, k, hk, ?_⟩
      rw [heq]
      change QRawLabel.A (2 * (value / 2)) = QRawLabel.A value
      exact congrArg QRawLabel.A hdecomp.symm

theorem targetAPhiOne_succ_eq_phi_val_succ {h : Nat} [NeZero h]
    (x : Fin h) :
    targetAPhiOne h (x.val + 1) = (phi h x).val + 1 := by
  simp [targetAPhiOne, phi]

theorem targetAQExpected32_oddA_return
    {m h : Nat} [NeZero h] (hm : m = 2 * h + 1) (hh : 6 ≤ h)
    (x : Fin h) :
    (targetAQExpected32 m h)^[targetAQExpected32OddATime h x]
        (targetAQOddA x) =
      targetAQOddA (phi h x) := by
  unfold targetAQExpected32OddATime targetAQOddA
  by_cases hx : x.val = 5
  · rw [if_pos hx]
    rw [show 2 * x.val + 1 = 11 by omega]
    rw [targetAQExpected32_A_six_excursion (m := m) (h := h) hm (by omega)]
    have hphi := phi_val_five x hx
    simp [hphi]
  · rw [if_neg hx]
    rw [targetAQExpected32_A_odd_two_step (m := m) (h := h)
      (x := x.val) (by omega)]
    have hphiOne := targetAPhiOne_succ_eq_phi_val_succ (h := h) x
    rw [hphiOne]
    congr

theorem targetARep1ToH_pos (h value : Nat) :
    1 ≤ targetARep1ToH h value := by
  unfold targetARep1ToH
  omega

theorem targetARep1ToH_le {h value : Nat} [NeZero h] :
    targetARep1ToH h value ≤ h := by
  unfold targetARep1ToH
  have hlt : (value - 1) % h < h := Nat.mod_lt _ (NeZero.pos h)
  omega

theorem targetAPhiOne_pos (h x : Nat) :
    1 ≤ targetAPhiOne h x := by
  unfold targetAPhiOne
  omega

theorem targetAPhiOne_le {h x : Nat} [NeZero h] :
    targetAPhiOne h x ≤ h := by
  unfold targetAPhiOne phiNat
  split
  · have hlt : (x - 1 + h - 3) % h < h := Nat.mod_lt _ (NeZero.pos h)
    omega
  · split
    · have hlt : (x - 1 + h - 8) % h < h := Nat.mod_lt _ (NeZero.pos h)
      omega
    · have hlt : (x - 1 + h - 5) % h < h := Nat.mod_lt _ (NeZero.pos h)
      omega

theorem targetATau23One_pos {h x : Nat} [NeZero h] :
    1 ≤ targetATau23One h x := by
  unfold targetATau23One
  by_cases hx3 : x ≤ 3
  · simp [hx3, targetARep1ToH_pos]
  · by_cases hx5 : x ≤ 5
    · simp [hx3, hx5, targetARep1ToH_pos]
    · by_cases hx6 : x = 6
      · simp [hx6, targetARep1ToH_pos]
      · simp [hx3, hx5, hx6]
        omega

theorem targetATau23One_le {h x : Nat} [NeZero h]
    (hx : x ≤ h) :
    targetATau23One h x ≤ h := by
  unfold targetATau23One
  by_cases hx3 : x ≤ 3
  · simp [hx3, targetARep1ToH_le]
  · by_cases hx5 : x ≤ 5
    · simp [hx3, hx5, targetARep1ToH_le]
    · by_cases hx6 : x = 6
      · simp [hx6, targetARep1ToH_le]
      · simp [hx3, hx5, hx6]
        omega

theorem targetAQExpectedB_valid {m value : Nat}
    (hv : (QRawLabel.B value).valid m) :
    (targetAQExpectedB m value).valid m := by
  rcases hv with ⟨hv1, hvm⟩
  by_cases hlt : value + 1 < m
  · simp [targetAQExpectedB, QRawLabel.valid, QRawLabel.B, hlt]
  · simp [targetAQExpectedB, QRawLabel.valid, QRawLabel.A, hlt]
    omega

theorem targetAQExpected23_valid {m h : Nat} [NeZero h]
    (hm : m = 2 * h + 1) (hh : 6 ≤ h) (label : QRawLabel)
    (hv : label.valid m) :
    (targetAQExpected23 m h label).valid m := by
  subst m
  rcases label with ⟨kind, value⟩
  cases kind
  · exact targetAQExpectedB_valid (m := 2 * h + 1) (value := value) hv
  · rcases hv with ⟨hv1, hvm⟩
    change 1 ≤ value at hv1
    change value < 2 * h + 1 at hvm
    unfold targetAQExpected23 QRawLabel.valid QRawLabel.A QRawLabel.B
    by_cases heven : value % 2 = 0
    · simp [heven]
      by_cases hx : value / 2 ≤ h - 1
      · simp [hx]
        omega
      · simp [hx]
        omega
    · simp [heven]
      have hxle : (value + 1) / 2 ≤ h := by omega
      have htpos := targetATau23One_pos (h := h) (x := (value + 1) / 2)
      have htle := targetATau23One_le (h := h) (x := (value + 1) / 2) hxle
      omega

theorem targetAQExpected32_valid {m h : Nat} [NeZero h]
    (hm : m = 2 * h + 1) (hh : 6 ≤ h) (label : QRawLabel)
    (hv : label.valid m) :
    (targetAQExpected32 m h label).valid m := by
  subst m
  rcases label with ⟨kind, value⟩
  cases kind
  · exact targetAQExpectedB_valid (m := 2 * h + 1) (value := value) hv
  · rcases hv with ⟨hv1, hvm⟩
    change 1 ≤ value at hv1
    change value < 2 * h + 1 at hvm
    unfold targetAQExpected32 QRawLabel.valid QRawLabel.A QRawLabel.B
    by_cases hodd : value % 2 = 1
    · simp [hodd]
      have hxle : (value + 1) / 2 ≤ h := by omega
      omega
    · simp [hodd]
      by_cases hx6 : value / 2 = 6
      · simp [hx6]
        omega
      · simp [hx6]
        have hp := targetAPhiOne_pos h (value / 2)
        have hl := targetAPhiOne_le (h := h) (x := value / 2)
        omega

abbrev QLabel (m : Nat) :=
  {label : QRawLabel // label.valid m}

namespace QLabel

def equivKindFin (m : Nat) : QLabel m ≃ QKind × Fin (m - 1) where
  toFun label :=
    (label.1.kind, ⟨label.1.value - 1, by
      rcases label.2 with ⟨hpos, hlt⟩
      omega⟩)
  invFun data :=
    ⟨⟨data.1, data.2.val + 1⟩, by
      constructor
      · change 1 ≤ data.2.val + 1
        omega
      · have hlt := data.2.isLt
        change data.2.val + 1 < m
        omega⟩
  left_inv label := by
    rcases label with ⟨⟨kind, value⟩, hv⟩
    rcases hv with ⟨hpos, hlt⟩
    apply Subtype.ext
    have hval : value - 1 + 1 = value := Nat.sub_add_cancel hpos
    cases kind <;> simp [hval]
  right_inv data := by
    rcases data with ⟨kind, value⟩
    simp

noncomputable instance (m : Nat) : Fintype (QLabel m) :=
  Fintype.ofEquiv (QKind × Fin (m - 1)) (equivKindFin m).symm

def expected23 {m h : Nat} [NeZero h]
    (hm : m = 2 * h + 1) (hh : 6 ≤ h) (label : QLabel m) :
    QLabel m :=
  ⟨targetAQExpected23 m h label.1,
    targetAQExpected23_valid hm hh label.1 label.2⟩

def expected32 {m h : Nat} [NeZero h]
    (hm : m = 2 * h + 1) (hh : 6 ≤ h) (label : QLabel m) :
    QLabel m :=
  ⟨targetAQExpected32 m h label.1,
    targetAQExpected32_valid hm hh label.1 label.2⟩

@[simp] theorem expected23_val {m h : Nat} [NeZero h]
    (hm : m = 2 * h + 1) (hh : 6 ≤ h) (label : QLabel m) :
    (expected23 hm hh label).1 = targetAQExpected23 m h label.1 :=
  rfl

@[simp] theorem expected32_val {m h : Nat} [NeZero h]
    (hm : m = 2 * h + 1) (hh : 6 ≤ h) (label : QLabel m) :
    (expected32 hm hh label).1 = targetAQExpected32 m h label.1 :=
  rfl

theorem expected32_iter_val {m h : Nat} [NeZero h]
    (hm : m = 2 * h + 1) (hh : 6 ≤ h) (n : Nat) (label : QLabel m) :
    (((expected32 hm hh)^[n]) label).1 =
      (targetAQExpected32 m h)^[n] label.1 := by
  induction n generalizing label with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [expected32_val]
      rw [ih label]

theorem expected23_iter_val {m h : Nat} [NeZero h]
    (hm : m = 2 * h + 1) (hh : 6 ≤ h) (n : Nat) (label : QLabel m) :
    (((expected23 hm hh)^[n]) label).1 =
      (targetAQExpected23 m h)^[n] label.1 := by
  induction n generalizing label with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [expected23_val]
      rw [ih label]

def oddA {m h : Nat} (hm : m = 2 * h + 1) (x : Fin h) : QLabel m :=
  ⟨targetAQOddA x, targetAQOddA_valid hm x⟩

@[simp] theorem oddA_val {m h : Nat}
    (hm : m = 2 * h + 1) (x : Fin h) :
    (oddA hm x).1 = targetAQOddA x :=
  rfl

theorem expected32_oddA_return {m h : Nat} [NeZero h]
    (hm : m = 2 * h + 1) (hh : 6 ≤ h) (x : Fin h) :
    ((expected32 hm hh)^[targetAQExpected32OddATime h x]) (oddA hm x) =
      oddA hm (phi h x) := by
  apply Subtype.ext
  rw [expected32_iter_val]
  exact targetAQExpected32_oddA_return hm hh x

theorem expected23_oddA_return {m h : Nat} [NeZero h]
    (hm : m = 2 * h + 1) (hh : 6 ≤ h) (x : Fin h) :
    ((expected23 hm hh)^[targetAQExpected23OddATime h x]) (oddA hm x) =
      oddA hm (phi h x) := by
  apply Subtype.ext
  rw [expected23_iter_val]
  exact targetAQExpected23_oddA_return hm hh x

theorem expected32_oddA_cover {m h : Nat} [NeZero h]
    (hm : m = 2 * h + 1) (hh : 6 ≤ h) (label : QLabel m) :
    ∃ x : Fin h, ∃ k : Nat,
      k < targetAQExpected32OddATime h x ∧
        ((expected32 hm hh)^[k]) (oddA hm x) = label := by
  rcases targetAQExpected32_oddA_cover hm hh label.1 label.2 with
    ⟨x, k, hk, heq⟩
  refine ⟨x, k, hk, ?_⟩
  apply Subtype.ext
  rw [expected32_iter_val]
  exact heq

theorem expected23_oddA_cover {m h : Nat} [NeZero h]
    (hm : m = 2 * h + 1) (hh : 6 ≤ h) (label : QLabel m) :
    ∃ x : Fin h, ∃ k : Nat,
      k < targetAQExpected23OddATime h x ∧
        ((expected23 hm hh)^[k]) (oddA hm x) = label := by
  rcases targetAQExpected23_oddA_cover hm hh label.1 label.2 with
    ⟨x, k, hk, heq⟩
  refine ⟨x, k, hk, ?_⟩
  apply Subtype.ext
  rw [expected23_iter_val]
  exact heq

theorem expected23_single_cycle_of_good {m h : Nat} [NeZero h]
    (hm : m = 2 * h + 1) (hh : 6 ≤ h) (hgood : goodPhiClass h) :
    IsSingleCycleMap (expected23 hm hh) := by
  exact single_cycle_of_return_cover_finite
    (f := expected23 hm hh)
    (base := oddA hm)
    (next := phi h)
    (time := targetAQExpected23OddATime h)
    (hreturn := expected23_oddA_return hm hh)
    (hcover := expected23_oddA_cover hm hh)
    (hnext := phi_single_cycle_of_good hh hgood)

theorem expected32_single_cycle_of_good {m h : Nat} [NeZero h]
    (hm : m = 2 * h + 1) (hh : 6 ≤ h) (hgood : goodPhiClass h) :
    IsSingleCycleMap (expected32 hm hh) := by
  exact single_cycle_of_return_cover_finite
    (f := expected32 hm hh)
    (base := oddA hm)
    (next := phi h)
    (time := targetAQExpected32OddATime h)
    (hreturn := expected32_oddA_return hm hh)
    (hcover := expected32_oddA_cover hm hh)
    (hnext := phi_single_cycle_of_good hh hgood)

end QLabel

def targetAQFirstReturn23EndomapFormula
    {m h : Nat} [NeZero h] (hm : m = 2 * h + 1) (hh : 6 ≤ h)
    (actual : QLabel m → QLabel m) : Prop :=
  ∀ label, actual label = QLabel.expected23 hm hh label

def targetAQFirstReturn32EndomapFormula
    {m h : Nat} [NeZero h] (hm : m = 2 * h + 1) (hh : 6 ≤ h)
    (actual : QLabel m → QLabel m) : Prop :=
  ∀ label, actual label = QLabel.expected32 hm hh label

def targetAQLift23
    {m h : Nat} [NeZero h] (hm : m = 2 * h + 1) (hh : 6 ≤ h)
    (actual : QRawLabel → QRawLabel)
    (hformula : targetAQFirstReturn23Formula m h actual) :
    QLabel m → QLabel m :=
  fun label =>
    ⟨actual label.1, by
      rw [hformula label.1 label.2]
      exact targetAQExpected23_valid hm hh label.1 label.2⟩

def targetAQLift32
    {m h : Nat} [NeZero h] (hm : m = 2 * h + 1) (hh : 6 ≤ h)
    (actual : QRawLabel → QRawLabel)
    (hformula : targetAQFirstReturn32Formula m h actual) :
    QLabel m → QLabel m :=
  fun label =>
    ⟨actual label.1, by
      rw [hformula label.1 label.2]
      exact targetAQExpected32_valid hm hh label.1 label.2⟩

theorem targetAQLift23_endomapFormula
    {m h : Nat} [NeZero h] (hm : m = 2 * h + 1) (hh : 6 ≤ h)
    {actual : QRawLabel → QRawLabel}
    (hformula : targetAQFirstReturn23Formula m h actual) :
    targetAQFirstReturn23EndomapFormula hm hh
      (targetAQLift23 hm hh actual hformula) := by
  intro label
  apply Subtype.ext
  exact hformula label.1 label.2

theorem targetAQLift32_endomapFormula
    {m h : Nat} [NeZero h] (hm : m = 2 * h + 1) (hh : 6 ≤ h)
    {actual : QRawLabel → QRawLabel}
    (hformula : targetAQFirstReturn32Formula m h actual) :
    targetAQFirstReturn32EndomapFormula hm hh
      (targetAQLift32 hm hh actual hformula) := by
  intro label
  apply Subtype.ext
  exact hformula label.1 label.2

theorem targetAQFirstReturn23EndomapFormula.single_cycle_of_good
    {m h : Nat} [NeZero h] (hm : m = 2 * h + 1) (hh : 6 ≤ h)
    {actual : QLabel m → QLabel m}
    (hformula : targetAQFirstReturn23EndomapFormula hm hh actual)
    (hgood : goodPhiClass h) :
    IsSingleCycleMap actual := by
  have hactual : actual = QLabel.expected23 hm hh := by
    funext label
    exact hformula label
  rw [hactual]
  exact QLabel.expected23_single_cycle_of_good hm hh hgood

theorem targetAQFirstReturn32EndomapFormula.single_cycle_of_good
    {m h : Nat} [NeZero h] (hm : m = 2 * h + 1) (hh : 6 ≤ h)
    {actual : QLabel m → QLabel m}
    (hformula : targetAQFirstReturn32EndomapFormula hm hh actual)
    (hgood : goodPhiClass h) :
    IsSingleCycleMap actual := by
  have hactual : actual = QLabel.expected32 hm hh := by
    funext label
    exact hformula label
  rw [hactual]
  exact QLabel.expected32_single_cycle_of_good hm hh hgood

theorem targetAQFirstReturn23Formula.lift_single_cycle_of_good
    {m h : Nat} [NeZero h] (hm : m = 2 * h + 1) (hh : 6 ≤ h)
    {actual : QRawLabel → QRawLabel}
    (hformula : targetAQFirstReturn23Formula m h actual)
    (hgood : goodPhiClass h) :
    IsSingleCycleMap (targetAQLift23 hm hh actual hformula) :=
  targetAQFirstReturn23EndomapFormula.single_cycle_of_good hm hh
    (targetAQLift23_endomapFormula hm hh hformula) hgood

theorem targetAQFirstReturn32Formula.lift_single_cycle_of_good
    {m h : Nat} [NeZero h] (hm : m = 2 * h + 1) (hh : 6 ≤ h)
    {actual : QRawLabel → QRawLabel}
    (hformula : targetAQFirstReturn32Formula m h actual)
    (hgood : goodPhiClass h) :
    IsSingleCycleMap (targetAQLift32 hm hh actual hformula) :=
  targetAQFirstReturn32EndomapFormula.single_cycle_of_good hm hh
    (targetAQLift32_endomapFormula hm hh hformula) hgood

example : targetAQExpected23 13 6 (QRawLabel.B 1) = QRawLabel.B 2 := rfl

example : targetAQExpected23 13 6 (QRawLabel.B 12) = QRawLabel.A 1 := rfl

example : targetAQExpected23 13 6 (QRawLabel.A 2) = QRawLabel.A 3 := rfl

example : targetAQExpected23 13 6 (QRawLabel.A 1) = QRawLabel.A 6 := rfl

example : targetAQExpected32 13 6 (QRawLabel.A 1) = QRawLabel.A 2 := rfl

example : targetAQExpected32 13 6 (QRawLabel.A 12) = QRawLabel.B 1 := rfl

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

theorem targetA_hmin_of_m_eq {m h : Nat}
    (hm : m = 2 * h + 1) (hodd_range : 13 ≤ m) :
    6 ≤ h := by
  omega

structure TargetASeamQuotientRemaining (m h : Nat) [NeZero m] [NeZero h] :
    Type where
  hm : m = 2 * h + 1
  hodd_range : 13 ≤ m
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

def TargetASeamQuotientRemaining.toPackage
    {m h : Nat} [NeZero m] [NeZero h]
    (rem : TargetASeamQuotientRemaining m h) :
    TargetASeamQuotientPackage m h where
  hm := rem.hm
  hodd_range := rem.hodd_range
  arithmetic := TargetASeamQuotientArithmetic.ofSixLe
    (targetA_hmin_of_m_eq rem.hm rem.hodd_range)
  q_hitting_23 := rem.q_hitting_23
  q_hitting_23_proof := rem.q_hitting_23_proof
  q_hitting_32 := rem.q_hitting_32
  q_hitting_32_proof := rem.q_hitting_32_proof
  q_first_return_23 := rem.q_first_return_23
  q_first_return_23_proof := rem.q_first_return_23_proof
  q_first_return_32 := rem.q_first_return_32
  q_first_return_32_proof := rem.q_first_return_32_proof
  length_sum_23 := rem.length_sum_23
  length_sum_23_proof := rem.length_sum_23_proof
  length_sum_32 := rem.length_sum_32
  length_sum_32_proof := rem.length_sum_32_proof

end TargetA
end Handoff
end D7Odd
