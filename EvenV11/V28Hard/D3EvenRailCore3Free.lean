import EvenV11.V28Hard.D3EvenRailSchedule
import EvenV11.V28Hard.TerminalA2IntervalSplice

/-!
# D3-even rail seam: the core cyclicity, case `3 ∤ m` (module 3a)

This file proves the three per-color core statements of the rail-seam
schedule for even `m ≥ 4` with `3 ∤ m`
(`docs/WILDE_SEARCH_20260610.md` §4 item 4; numeric ground truth:
`scripts/search_d3_even_dir.py construct` / `core3free`):

* **`railCore_singleCycle_of_not_dvd`**: for every color `c`, the conjugated
  core map `w ↦ rhoRoot c w + driftVec m c` is a single `m²`-cycle on the
  standard root section `Fin 2 → ZMod m`.

Together with `D3EvenRailSchedule.railCycleData` this closes RF3 for the
rail-seam schedule in the `3 ∤ m` case.

The proof is a two-level interval splice (engine:
`TerminalA2IntervalSplice.single_cycle_of_interval_splice`), entirely in the
manuscript pair coordinates `TerminalQ m`, bridged to the root section at
the very end through `rootPairEquiv`:

* **Level 1** (points): the core map `G_c = T_{u_c} ∘ ρ_c` translates by the
  drift `u_c` until the orbit hits the active seam
  (`D3EvenRailSeam.seamPoint`), then `ρ_c` kicks it one seam rank forward.
  The orbit therefore splits into `2m` straight `u_c`-rays, one per seam
  label: interval `k` starts at `head k = seamPoint c (k+1) + u_c`, has the
  explicit length `lenNat c m k`, and ends one kick after the first active
  ray point `seamPoint c (σ_c k)`.  The label successor `σ_c = sigNat c m`
  and the lengths are closed-form piecewise affine maps (verified against
  the script for all even `3 ∤ m` moduli up to `34`).
* **Level 2** (labels): `σ_c` itself is spliced along the `m/2`-element
  transversal `ι_c : ZMod (m/2) → Fin 2m` with constant interval length
  `4`: `σ_c⁴ ∘ ι_c = ι_c ∘ (+3)`, and `+3` is a single cycle on
  `ZMod (m/2)` precisely because `3 ∤ m` — this is the only place where the
  hypothesis `3 ∤ m` enters; evenness enters through the parity branches of
  `σ_c` and the transversal size `m/2`.

The generic argument needs `m ≥ 8`; `m = 4` (the only other even `3 ∤ m`
modulus) is closed by an explicit `16`-point orbit-rank certificate by
`decide`.  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace EvenV11
namespace V28Hard
namespace D3EvenRailCore3Free

open Shared
open TerminalA2LowMod
open D3TerminalA2Parametric
open D3EvenRailSeam
open D3EvenRailSchedule
open TerminalA2IntervalSplice

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## Cast toolkit: every coordinate is a `Nat`-cast -/

section Toolkit

variable {m : Nat} [NeZero m]

private theorem valNat (a : Nat) : ((a : Nat) : ZMod m).val = a % m :=
  ZMod.val_natCast m a

private theorem valNat_lt {a : Nat} (h : a < m) :
    ((a : Nat) : ZMod m).val = a :=
  ZMod.val_natCast_of_lt h

/-- Drop an explicit multiple of `m` under a `Nat` cast. -/
private theorem castShift {a b : Nat} (k : Nat) (h : a = b + k * m) :
    ((a : Nat) : ZMod m) = ((b : Nat) : ZMod m) := by
  rw [h]
  push_cast [ZMod.natCast_self]
  ring

/-- Four-range value table for casts below `4m`. -/
private theorem val_cases4m {a : Nat} (h : a < 4 * m) :
    (a < m ∧ ((a : Nat) : ZMod m).val = a) ∨
      (m ≤ a ∧ a < 2 * m ∧ ((a : Nat) : ZMod m).val = a - m) ∨
      (2 * m ≤ a ∧ a < 3 * m ∧ ((a : Nat) : ZMod m).val = a - 2 * m) ∨
      (3 * m ≤ a ∧ ((a : Nat) : ZMod m).val = a - 3 * m) := by
  rcases Nat.lt_or_ge a m with h1 | h1
  · exact Or.inl ⟨h1, valNat_lt h1⟩
  rcases Nat.lt_or_ge a (2 * m) with h2 | h2
  · refine Or.inr (Or.inl ⟨h1, h2, ?_⟩)
    rw [castShift 1 (show a = (a - m) + 1 * m by omega)]
    exact valNat_lt (by omega)
  rcases Nat.lt_or_ge a (3 * m) with h3 | h3
  · refine Or.inr (Or.inr (Or.inl ⟨h2, h3, ?_⟩))
    rw [castShift 2 (show a = (a - 2 * m) + 2 * m by omega)]
    exact valNat_lt (by omega)
  · refine Or.inr (Or.inr (Or.inr ⟨h3, ?_⟩))
    rw [castShift 3 (show a = (a - 3 * m) + 3 * m by omega)]
    exact valNat_lt (by omega)

/-- Uniform cast congruence: equality up to an explicit multiple of `m`
(in either direction), dischargeable by `omega`. -/
private theorem castMod {a b : Nat}
    (h : a = b ∨ a = b + 1 * m ∨ a = b + 2 * m ∨ a = b + 3 * m ∨
      b = a + 1 * m ∨ b = a + 2 * m ∨ b = a + 3 * m) :
    ((a : Nat) : ZMod m) = ((b : Nat) : ZMod m) := by
  rcases h with h | h | h | h | h | h | h
  · rw [h]
  · exact castShift 1 h
  · exact castShift 2 h
  · exact castShift 3 h
  · exact (castShift 1 h).symm
  · exact (castShift 2 h).symm
  · exact (castShift 3 h).symm

private theorem val_one (hm : 4 ≤ m) : (1 : ZMod m).val = 1 := by
  rw [← Nat.cast_one]
  exact valNat_lt (by omega)

private theorem val_two (hm : 4 ≤ m) : (2 : ZMod m).val = 2 := by
  rw [← Nat.cast_two]
  exact valNat_lt (by omega)

private theorem val_three (hm : 4 ≤ m) : (3 : ZMod m).val = 3 := by
  rw [show (3 : ZMod m) = ((3 : Nat) : ZMod m) by push_cast; ring]
  exact valNat_lt (by omega)

private theorem neg_one_cast (hm : 4 ≤ m) :
    (-1 : ZMod m) = ((m - 1 : Nat) : ZMod m) := by
  have h : ((m - 1 : Nat) : ZMod m) + 1 = 0 := by
    rw [show (1 : ZMod m) = ((1 : Nat) : ZMod m) by push_cast; ring]
    rw [show ((m - 1 : Nat) : ZMod m) + ((1 : Nat) : ZMod m)
        = ((m - 1 + 1 : Nat) : ZMod m) by push_cast; ring]
    rw [castShift (b := 0) 1 (by omega)]
    push_cast
    ring
  linear_combination -h

private theorem neg_two_cast (hm : 4 ≤ m) :
    (-2 : ZMod m) = ((m - 2 : Nat) : ZMod m) := by
  have h : ((m - 2 : Nat) : ZMod m) + 2 = 0 := by
    rw [show (2 : ZMod m) = ((2 : Nat) : ZMod m) by push_cast; ring]
    rw [show ((m - 2 : Nat) : ZMod m) + ((2 : Nat) : ZMod m)
        = ((m - 2 + 2 : Nat) : ZMod m) by push_cast; ring]
    rw [castShift (b := 0) 1 (by omega)]
    push_cast
    ring
  linear_combination -h

private theorem val_neg_one (hm : 4 ≤ m) : (-1 : ZMod m).val = m - 1 := by
  rw [neg_one_cast hm]
  exact valNat_lt (by omega)

private theorem val_neg_two (hm : 4 ≤ m) : (-2 : ZMod m).val = m - 2 := by
  rw [neg_two_cast hm]
  exact valNat_lt (by omega)

end Toolkit

/-! ## The `cpt` normal form: pairs of `Nat`-casts -/

section Cpt

variable {m : Nat} [NeZero m]

/-- Canonical pair-coordinate point with `Nat` data. -/
private def cpt (a b : Nat) : TerminalQ m :=
  (((a : Nat) : ZMod m), ((b : Nat) : ZMod m))

private theorem cpt_add (a b p q : Nat) :
    (cpt a b : TerminalQ m) + cpt p q = cpt (a + p) (b + q) := by
  unfold cpt
  rw [Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> (push_cast; ring)

private theorem cpt_congr {a b a' b' : Nat}
    (h1 : ((a : Nat) : ZMod m) = ((a' : Nat) : ZMod m))
    (h2 : ((b : Nat) : ZMod m) = ((b' : Nat) : ZMod m)) :
    (cpt a b : TerminalQ m) = cpt a' b' := by
  unfold cpt
  rw [h1, h2]

/-- The three conjugated drifts for `3 ∤ m`, in `cpt` form:
`u₀ = (1,1)`, `u₁ = (−2,1)`, `u₂ = (1,−2)`. -/
private def uVec (m : Nat) [NeZero m] : Fin 3 → TerminalQ m
  | 0 => cpt 1 1
  | 1 => cpt (2 * m - 2) 1
  | 2 => cpt 1 (2 * m - 2)

private theorem cpt_add_u0 (hm : 4 ≤ m) (a b : Nat) :
    ∀ j : Nat, (cpt a b : TerminalQ m) + j • uVec m 0
      = cpt (a + j) (b + j)
  | 0 => by
      rw [zero_nsmul, add_zero, Nat.add_zero, Nat.add_zero]
  | j + 1 => by
      rw [succ_nsmul, ← add_assoc, cpt_add_u0 hm a b j]
      show (cpt (a + j) (b + j) : TerminalQ m) + cpt 1 1 = _
      rw [cpt_add]
      exact cpt_congr (castShift 0 (by omega)) (castShift 0 (by omega))

private theorem cpt_add_u1 (hm : 4 ≤ m) (a b : Nat) :
    ∀ j : Nat, j ≤ m → (cpt a b : TerminalQ m) + j • uVec m 1
      = cpt (a + (2 * m - 2 * j)) (b + j)
  | 0, _ => by
      rw [zero_nsmul, add_zero, Nat.add_zero]
      exact cpt_congr (castShift (a := a + (2 * m - 2 * 0)) 2
        (by omega)).symm rfl
  | j + 1, hj => by
      rw [succ_nsmul, ← add_assoc, cpt_add_u1 hm a b j (by omega)]
      show (cpt (a + (2 * m - 2 * j)) (b + j) : TerminalQ m)
          + cpt (2 * m - 2) 1 = _
      rw [cpt_add]
      exact cpt_congr (castShift 2 (by omega)) (castShift 0 (by omega))

private theorem cpt_add_u2 (hm : 4 ≤ m) (a b : Nat) :
    ∀ j : Nat, j ≤ m → (cpt a b : TerminalQ m) + j • uVec m 2
      = cpt (a + j) (b + (2 * m - 2 * j))
  | 0, _ => by
      rw [zero_nsmul, add_zero, Nat.add_zero]
      exact cpt_congr rfl (castShift (a := b + (2 * m - 2 * 0)) 2
        (by omega)).symm
  | j + 1, hj => by
      rw [succ_nsmul, ← add_assoc, cpt_add_u2 hm a b j (by omega)]
      show (cpt (a + j) (b + (2 * m - 2 * j)) : TerminalQ m)
          + cpt 1 (2 * m - 2) = _
      rw [cpt_add]
      exact cpt_congr (castShift 0 (by omega)) (castShift 2 (by omega))

private theorem fin3_cases (c : Fin 3) : c = 0 ∨ c = 1 ∨ c = 2 := by
  revert c
  decide

/-- The conjugated drift table of module 2 in `cpt` form, case `3 ∤ m`. -/
private theorem driftPair_eq_uVec (hm : 4 ≤ m) (h3 : m % 3 ≠ 0)
    (c : Fin 3) : driftPair m c = uVec m c := by
  rcases fin3_cases c with rfl | rfl | rfl
  · rw [driftPair_ne_zero h3]
    show _ = (cpt 1 1 : TerminalQ m)
    unfold cpt
    rw [Prod.mk.injEq]
    constructor <;> (push_cast; ring)
  · rw [driftPair_ne_one h3]
    show _ = (cpt (2 * m - 2) 1 : TerminalQ m)
    unfold cpt
    rw [Prod.mk.injEq]
    refine ⟨(castShift (a := 2 * m - 2) (b := m - 2) 1 (by omega)).symm,
      ?_⟩
    push_cast
    ring
  · rw [driftPair_ne_two h3]
    show _ = (cpt 1 (2 * m - 2) : TerminalQ m)
    unfold cpt
    rw [Prod.mk.injEq]
    refine ⟨?_,
      (castShift (a := 2 * m - 2) (b := m - 2) 1 (by omega)).symm⟩
    push_cast
    ring

end Cpt

/-! ## Rail membership in `Nat` value form -/

section ValForms

variable {m : Nat} [NeZero m]

private theorem memP_val (hm : 4 ≤ m) {w : TerminalQ m} (h : memP w) :
    (w.1.val = 0 ∧ w.2.val = 0) ∨
      (3 ≤ w.1.val ∧ w.1.val + w.2.val = m) ∨
      (w.1.val = 1 ∧ w.2.val = m - 2) ∨
      (w.1.val = 2 ∧ w.2.val = m - 1) := by
  have h1 := ZMod.val_lt w.1
  have h2 := ZMod.val_lt w.2
  rcases h with h | ⟨hsum, hx⟩ | h | h
  · subst h
    exact Or.inl ⟨ZMod.val_zero, ZMod.val_zero⟩
  · have hv := congrArg ZMod.val hsum
    rw [ZMod.val_add, ZMod.val_zero] at hv
    refine Or.inr (Or.inl ⟨hx, ?_⟩)
    rcases Nat.lt_or_ge (w.1.val + w.2.val) m with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hv
      omega
    · rw [Nat.mod_eq_sub_mod hge,
        Nat.mod_eq_of_lt (by omega : w.1.val + w.2.val - m < m)] at hv
      omega
  · subst h
    exact Or.inr (Or.inr (Or.inl ⟨val_one hm, val_neg_two hm⟩))
  · subst h
    exact Or.inr (Or.inr (Or.inr ⟨val_two hm, val_neg_one hm⟩))

private theorem memQ_val (hm : 4 ≤ m) {w : TerminalQ m} (h : memQ w) :
    (w.2.val = m - 1 ∧ (w.1.val = 0 ∨ 3 ≤ w.1.val)) ∨
      (w.1.val = 1 ∧ w.2.val = 0) ∨
      (w.1.val = 2 ∧ w.2.val = m - 2) := by
  rcases h with ⟨h1, h2⟩ | h | h
  · have hv := congrArg ZMod.val h1
    rw [val_neg_one hm] at hv
    rcases h2 with h2 | h2
    · have hv1 := congrArg ZMod.val h2
      rw [ZMod.val_zero] at hv1
      exact Or.inl ⟨hv, Or.inl hv1⟩
    · exact Or.inl ⟨hv, Or.inr h2⟩
  · subst h
    exact Or.inr (Or.inl ⟨val_one hm, ZMod.val_zero⟩)
  · subst h
    exact Or.inr (Or.inr ⟨val_two hm, val_neg_two hm⟩)

private theorem memS_val (hm : 4 ≤ m) {w : TerminalQ m} (h : memS w) :
    (w.1.val = 2 ∧ w.2.val ≤ m - 3) ∨
      (w.1.val = 1 ∧ w.2.val = m - 1) ∨
      (w.1.val = 3 ∧ w.2.val = m - 2) := by
  rcases h with ⟨h1, h2⟩ | h | h
  · have hv := congrArg ZMod.val h1
    rw [val_two hm] at hv
    exact Or.inl ⟨hv, h2⟩
  · subst h
    exact Or.inr (Or.inl ⟨val_one hm, val_neg_one hm⟩)
  · subst h
    exact Or.inr (Or.inr ⟨val_three hm, val_neg_two hm⟩)

/-- Color-0 active set (`P ∪ Q`) over a `cpt` point, in pure `Nat` form. -/
private theorem active0_cpt (hm : 4 ≤ m) {a b : Nat}
    (h : activePred 0 (cpt a b : TerminalQ m)) :
    (((a : Nat) : ZMod m).val = 0 ∧ ((b : Nat) : ZMod m).val = 0) ∨
      (3 ≤ ((a : Nat) : ZMod m).val ∧
        ((a : Nat) : ZMod m).val + ((b : Nat) : ZMod m).val = m) ∨
      (((a : Nat) : ZMod m).val = 1 ∧ ((b : Nat) : ZMod m).val = m - 2) ∨
      (((a : Nat) : ZMod m).val = 2 ∧ ((b : Nat) : ZMod m).val = m - 1) ∨
      (((b : Nat) : ZMod m).val = m - 1 ∧
        (((a : Nat) : ZMod m).val = 0 ∨ 3 ≤ ((a : Nat) : ZMod m).val)) ∨
      (((a : Nat) : ZMod m).val = 1 ∧ ((b : Nat) : ZMod m).val = 0) ∨
      (((a : Nat) : ZMod m).val = 2 ∧
        ((b : Nat) : ZMod m).val = m - 2) := by
  rcases h with hp | hq
  · rcases memP_val hm hp with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases memQ_val hm hq with h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

/-- Color-1 active set (`P ∪ S`) over a `cpt` point, in pure `Nat` form. -/
private theorem active1_cpt (hm : 4 ≤ m) {a b : Nat}
    (h : activePred 1 (cpt a b : TerminalQ m)) :
    (((a : Nat) : ZMod m).val = 0 ∧ ((b : Nat) : ZMod m).val = 0) ∨
      (3 ≤ ((a : Nat) : ZMod m).val ∧
        ((a : Nat) : ZMod m).val + ((b : Nat) : ZMod m).val = m) ∨
      (((a : Nat) : ZMod m).val = 1 ∧ ((b : Nat) : ZMod m).val = m - 2) ∨
      (((a : Nat) : ZMod m).val = 2 ∧ ((b : Nat) : ZMod m).val = m - 1) ∨
      (((a : Nat) : ZMod m).val = 2 ∧ ((b : Nat) : ZMod m).val ≤ m - 3) ∨
      (((a : Nat) : ZMod m).val = 1 ∧ ((b : Nat) : ZMod m).val = m - 1) ∨
      (((a : Nat) : ZMod m).val = 3 ∧
        ((b : Nat) : ZMod m).val = m - 2) := by
  rcases h with hp | hs
  · rcases memP_val hm hp with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases memS_val hm hs with h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

/-- Color-2 active set (`Q ∪ S`) over a `cpt` point, in pure `Nat` form. -/
private theorem active2_cpt (hm : 4 ≤ m) {a b : Nat}
    (h : activePred 2 (cpt a b : TerminalQ m)) :
    (((b : Nat) : ZMod m).val = m - 1 ∧
        (((a : Nat) : ZMod m).val = 0 ∨ 3 ≤ ((a : Nat) : ZMod m).val)) ∨
      (((a : Nat) : ZMod m).val = 1 ∧ ((b : Nat) : ZMod m).val = 0) ∨
      (((a : Nat) : ZMod m).val = 2 ∧ ((b : Nat) : ZMod m).val = m - 2) ∨
      (((a : Nat) : ZMod m).val = 2 ∧ ((b : Nat) : ZMod m).val ≤ m - 3) ∨
      (((a : Nat) : ZMod m).val = 1 ∧ ((b : Nat) : ZMod m).val = m - 1) ∨
      (((a : Nat) : ZMod m).val = 3 ∧
        ((b : Nat) : ZMod m).val = m - 2) := by
  rcases h with hq | hs
  · rcases memQ_val hm hq with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases memS_val hm hs with h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end ValForms

/-! ## Seam point evaluations in `cpt` form -/

section SeamEval

variable {m : Nat} [NeZero m]

private theorem sp0_anti (hm : 4 ≤ m) {n : Nat} (hn : n ≤ m - 2) :
    seamPoint0Nat m n = (cpt (2 * m - n) n : TerminalQ m) := by
  unfold seamPoint0Nat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]
  unfold cpt
  rw [Prod.mk.injEq]
  refine ⟨?_, rfl⟩
  have h : ((n : Nat) : ZMod m) + ((2 * m - n : Nat) : ZMod m) = 0 := by
    rw [show ((n : Nat) : ZMod m) + ((2 * m - n : Nat) : ZMod m)
        = ((n + (2 * m - n) : Nat) : ZMod m) by push_cast; ring]
    rw [castShift (b := 0) 2 (by omega)]
    push_cast
    ring
  linear_combination -h

private theorem sp0_mid (hm : 4 ≤ m) {n : Nat} (hn : n = m - 1) :
    seamPoint0Nat m n = (cpt 1 (m - 2) : TerminalQ m) := by
  unfold seamPoint0Nat
  rw [if_pos hn]
  unfold cpt
  rw [Prod.mk.injEq]
  exact ⟨by push_cast; ring, neg_two_cast hm⟩

private theorem sp0_row (hm : 4 ≤ m) {n : Nat} (h1 : m ≤ n)
    (h2 : n ≤ 2 * m - 3) :
    seamPoint0Nat m n = (cpt (2 * m - n) (m - 1) : TerminalQ m) := by
  unfold seamPoint0Nat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]
  unfold cpt
  rw [Prod.mk.injEq]
  constructor
  · have h : ((n : Nat) : ZMod m) + ((2 * m - n : Nat) : ZMod m) = 0 := by
      rw [show ((n : Nat) : ZMod m) + ((2 * m - n : Nat) : ZMod m)
          = ((n + (2 * m - n) : Nat) : ZMod m) by push_cast; ring]
      rw [castShift (b := 0) 2 (by omega)]
      push_cast
      ring
    linear_combination -h
  · exact neg_one_cast hm

private theorem sp0_rowEnd (hm : 4 ≤ m) {n : Nat} (hn : n = 2 * m - 2) :
    seamPoint0Nat m n = (cpt 2 (m - 1) : TerminalQ m) := by
  unfold seamPoint0Nat
  rw [if_neg (by omega), if_pos hn]
  unfold cpt
  rw [Prod.mk.injEq]
  exact ⟨by push_cast; ring, neg_one_cast hm⟩

private theorem sp0_last (hm : 4 ≤ m) {n : Nat} (hn : n = 2 * m - 1) :
    seamPoint0Nat m n = (cpt 1 0 : TerminalQ m) := by
  unfold seamPoint0Nat
  rw [if_neg (by omega), if_neg (by omega), if_pos hn]
  unfold cpt
  rw [Prod.mk.injEq]
  constructor <;> (push_cast; ring)

private theorem sp1_zero (hm : 4 ≤ m) {n : Nat} (hn : n = 0) :
    seamPoint1Nat m n = (cpt 0 0 : TerminalQ m) := by
  unfold seamPoint1Nat
  rw [if_pos hn]
  unfold cpt
  rw [Prod.mk.injEq]
  constructor <;> (push_cast; ring)

private theorem sp1_one (hm : 4 ≤ m) {n : Nat} (hn : n = 1) :
    seamPoint1Nat m n = (cpt 1 (m - 1) : TerminalQ m) := by
  unfold seamPoint1Nat
  rw [if_neg (by omega), if_pos hn]
  unfold cpt
  rw [Prod.mk.injEq]
  exact ⟨by push_cast; ring, neg_one_cast hm⟩

private theorem sp1_two (hm : 4 ≤ m) {n : Nat} (hn : n = 2) :
    seamPoint1Nat m n = (cpt 1 (m - 2) : TerminalQ m) := by
  unfold seamPoint1Nat
  rw [if_neg (by omega), if_neg (by omega), if_pos hn]
  unfold cpt
  rw [Prod.mk.injEq]
  exact ⟨by push_cast; ring, neg_two_cast hm⟩

private theorem sp1_col (hm : 4 ≤ m) {n : Nat} (h1 : 3 ≤ n) (h2 : n ≤ m) :
    seamPoint1Nat m n = (cpt 2 (2 * m - n) : TerminalQ m) := by
  unfold seamPoint1Nat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos h2]
  unfold cpt
  rw [Prod.mk.injEq]
  constructor
  · push_cast
    ring
  · have h : ((n : Nat) : ZMod m) + ((2 * m - n : Nat) : ZMod m) = 0 := by
      rw [show ((n : Nat) : ZMod m) + ((2 * m - n : Nat) : ZMod m)
          = ((n + (2 * m - n) : Nat) : ZMod m) by push_cast; ring]
      rw [castShift (b := 0) 2 (by omega)]
      push_cast
      ring
    linear_combination -h

private theorem sp1_colEnd (hm : 4 ≤ m) {n : Nat} (hn : n = m + 1) :
    seamPoint1Nat m n = (cpt 2 (m - 1) : TerminalQ m) := by
  unfold seamPoint1Nat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hn]
  unfold cpt
  rw [Prod.mk.injEq]
  exact ⟨by push_cast; ring, neg_one_cast hm⟩

private theorem sp1_hop (hm : 4 ≤ m) {n : Nat} (hn : n = m + 2) :
    seamPoint1Nat m n = (cpt 3 (m - 2) : TerminalQ m) := by
  unfold seamPoint1Nat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos hn]
  unfold cpt
  rw [Prod.mk.injEq]
  exact ⟨by push_cast; ring, neg_two_cast hm⟩

private theorem sp1_anti (hm : 4 ≤ m) {n : Nat} (h1 : m + 3 ≤ n)
    (h2 : n ≤ 2 * m - 1) :
    seamPoint1Nat m n = (cpt (n - m) (2 * m - n) : TerminalQ m) := by
  unfold seamPoint1Nat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  unfold cpt
  rw [Prod.mk.injEq]
  constructor
  · exact castShift (a := n) (b := n - m) 1 (by omega)
  · have h : ((n : Nat) : ZMod m) + ((2 * m - n : Nat) : ZMod m) = 0 := by
      rw [show ((n : Nat) : ZMod m) + ((2 * m - n : Nat) : ZMod m)
          = ((n + (2 * m - n) : Nat) : ZMod m) by push_cast; ring]
      rw [castShift (b := 0) 2 (by omega)]
      push_cast
      ring
    linear_combination -h

private theorem sp2_col (hm : 4 ≤ m) {n : Nat} (hn : n ≤ m - 2) :
    seamPoint2Nat m n = (cpt 2 n : TerminalQ m) := by
  unfold seamPoint2Nat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos hn]
  unfold cpt
  rw [Prod.mk.injEq]
  exact ⟨by push_cast; ring, rfl⟩

private theorem sp2_hop (hm : 4 ≤ m) {n : Nat} (hn : n = m - 1) :
    seamPoint2Nat m n = (cpt 3 (m - 2) : TerminalQ m) := by
  unfold seamPoint2Nat
  rw [if_pos hn]
  unfold cpt
  rw [Prod.mk.injEq]
  exact ⟨by push_cast; ring, neg_two_cast hm⟩

private theorem sp2_row (hm : 4 ≤ m) {n : Nat} (h1 : m ≤ n)
    (h2 : n ≤ 2 * m - 4) :
    seamPoint2Nat m n = (cpt (n + 3 - m) (m - 1) : TerminalQ m) := by
  unfold seamPoint2Nat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]
  unfold cpt
  rw [Prod.mk.injEq]
  constructor
  · rw [show ((n : Nat) : ZMod m) + 3
        = ((n + 3 : Nat) : ZMod m) by push_cast; ring]
    exact castShift (a := n + 3) (b := n + 3 - m) 1 (by omega)
  · exact neg_one_cast hm

private theorem sp2_rowZero (hm : 4 ≤ m) {n : Nat} (hn : n = 2 * m - 3) :
    seamPoint2Nat m n = (cpt 0 (m - 1) : TerminalQ m) := by
  unfold seamPoint2Nat
  rw [if_neg (by omega), if_pos hn]
  unfold cpt
  rw [Prod.mk.injEq]
  exact ⟨by push_cast; ring, neg_one_cast hm⟩

private theorem sp2_preLast (hm : 4 ≤ m) {n : Nat} (hn : n = 2 * m - 2) :
    seamPoint2Nat m n = (cpt 1 (m - 1) : TerminalQ m) := by
  unfold seamPoint2Nat
  rw [if_neg (by omega), if_neg (by omega), if_pos hn]
  unfold cpt
  rw [Prod.mk.injEq]
  exact ⟨by push_cast; ring, neg_one_cast hm⟩

private theorem sp2_last (hm : 4 ≤ m) {n : Nat} (hn : n = 2 * m - 1) :
    seamPoint2Nat m n = (cpt 1 0 : TerminalQ m) := by
  unfold seamPoint2Nat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hn]
  unfold cpt
  rw [Prod.mk.injEq]
  constructor <;> (push_cast; ring)

end SeamEval

/-! ## The label successor `σ_c` and the interval lengths -/

/-- Label successor table, color 0 (`3 ∤ m`, even `m ≥ 8`). -/
def sig0 (m k : Nat) : Nat :=
  if k ≤ m / 2 - 3 then k + m / 2 + 1
  else if k = m / 2 - 2 then m / 2 - 1
  else if k ≤ m - 3 then 2 * k + 3
  else if k = m - 2 then 2 * m - 2
  else if k = m - 1 then 2 * m - 1
  else if k = m then 0
  else if k = 2 * m - 3 then m - 1
  else if k = 2 * m - 2 then m
  else if k = 2 * m - 1 then m / 2
  else if k % 2 = 1 then k + 1
  else (k - m) / 2

/-- Interval length table, color 0. -/
def len0 (m k : Nat) : Nat :=
  if k ≤ m / 2 - 3 then m / 2
  else if k = m / 2 - 2 then m
  else if k ≤ m - 3 then m - 2 - k
  else if k = m - 2 then 1
  else if k = m - 1 then 1
  else if k = m then 1
  else if k = 2 * m - 3 then m - 1
  else if k = 2 * m - 2 then m - 1
  else if k = 2 * m - 1 then m / 2
  else if k % 2 = 1 then m
  else (k - m) / 2 + 1

/-- Label successor table, color 1. -/
def sig1 (m k : Nat) : Nat :=
  if k = 0 then m + 2
  else if k = 1 then m + 3
  else if k ≤ m / 2 then k + m / 2 + 1
  else if k = m / 2 + 1 then m / 2 + 2
  else if k ≤ m - 1 then 2 * k
  else if k ≤ m + 3 then k - m
  else if k = 2 * m - 1 then m / 2 + 1
  else if k % 2 = 0 then k + 1
  else (k - m + 3) / 2

/-- Interval length table, color 1. -/
def len1 (m k : Nat) : Nat :=
  if k = 0 then m - 1
  else if k = 1 then m - 1
  else if k ≤ m / 2 then m / 2
  else if k = m / 2 + 1 then m
  else if k ≤ m - 1 then m + 1 - k
  else if k ≤ m + 3 then 1
  else if k = 2 * m - 1 then m / 2 - 1
  else if k % 2 = 0 then m
  else (k - m - 1) / 2

/-- Label successor table, color 2. -/
def sig2 (m k : Nat) : Nat :=
  if k = 0 then m
  else if k ≤ m - 4 then (if k % 2 = 1 then k + 1 else k / 2 + m)
  else if k = m - 3 then 2 * m - 1
  else if k = m - 2 then 0
  else if k = m - 1 then m + m / 2
  else if k ≤ m + m / 2 - 3 then k + m / 2 + 1
  else if k = m + m / 2 - 2 then k + 1
  else if k ≤ 2 * m - 3 then 2 * k + 3 - 3 * m
  else if k = 2 * m - 2 then m - 2
  else m - 1

/-- Interval length table, color 2. -/
def len2 (m k : Nat) : Nat :=
  if k = 0 then 1
  else if k ≤ m - 4 then (if k % 2 = 1 then m else k / 2 + 1)
  else if k = m - 3 then m - 1
  else if k = m - 2 then m - 1
  else if k = m - 1 then m / 2
  else if k ≤ m + m / 2 - 3 then m / 2
  else if k = m + m / 2 - 2 then m
  else if k ≤ 2 * m - 3 then 2 * m - 2 - k
  else 1

section SigBounds

private theorem sig0_lt {m k : Nat} (hm : 8 ≤ m) (he : m % 2 = 0)
    (hk : k < 2 * m) : sig0 m k < 2 * m := by
  unfold sig0
  split_ifs <;> omega

private theorem sig1_lt {m k : Nat} (hm : 8 ≤ m) (he : m % 2 = 0)
    (hk : k < 2 * m) : sig1 m k < 2 * m := by
  unfold sig1
  split_ifs <;> omega

private theorem sig2_lt {m k : Nat} (hm : 8 ≤ m) (he : m % 2 = 0)
    (hk : k < 2 * m) : sig2 m k < 2 * m := by
  unfold sig2
  split_ifs <;> omega

private theorem len0_pos {m k : Nat} (hm : 8 ≤ m) (he : m % 2 = 0)
    (hk : k < 2 * m) : 0 < len0 m k := by
  unfold len0
  split_ifs <;> omega

private theorem len1_pos {m k : Nat} (hm : 8 ≤ m) (he : m % 2 = 0)
    (hk : k < 2 * m) : 0 < len1 m k := by
  unfold len1
  split_ifs <;> omega

private theorem len2_pos {m k : Nat} (hm : 8 ≤ m) (he : m % 2 = 0)
    (hk : k < 2 * m) : 0 < len2 m k := by
  unfold len2
  split_ifs <;> omega

end SigBounds

/-- The per-color label successor table. -/
def sigNat (c : Fin 3) (m k : Nat) : Nat :=
  if c = 0 then sig0 m k else if c = 1 then sig1 m k else sig2 m k

/-- The per-color interval lengths. -/
def lenNat (c : Fin 3) (m k : Nat) : Nat :=
  if c = 0 then len0 m k else if c = 1 then len1 m k else len2 m k

/-- The label successor as a self-map of `Fin (2m)`. -/
def sigF (c : Fin 3) (m : Nat) (k : Fin (2 * m)) : Fin (2 * m) :=
  ⟨sigNat c m k.val % (2 * m),
    Nat.mod_lt _ (by have := k.isLt; omega)⟩

section SigFLemmas

private theorem sigNat_zero (m k : Nat) : sigNat 0 m k = sig0 m k := rfl

private theorem sigNat_one (m k : Nat) : sigNat 1 m k = sig1 m k := rfl

private theorem sigNat_two (m k : Nat) : sigNat 2 m k = sig2 m k := rfl

private theorem lenNat_zero (m k : Nat) : lenNat 0 m k = len0 m k := rfl

private theorem lenNat_one (m k : Nat) : lenNat 1 m k = len1 m k := rfl

private theorem lenNat_two (m k : Nat) : lenNat 2 m k = len2 m k := rfl

private theorem sigF_val {m : Nat} (hm : 8 ≤ m) (he : m % 2 = 0)
    (c : Fin 3) (k : Fin (2 * m)) :
    (sigF c m k).val = sigNat c m k.val := by
  have hk := k.isLt
  refine Nat.mod_eq_of_lt ?_
  fin_cases c
  · exact sig0_lt hm he hk
  · exact sig1_lt hm he hk
  · exact sig2_lt hm he hk

private theorem lenF_pos {m : Nat} (hm : 8 ≤ m) (he : m % 2 = 0)
    (c : Fin 3) (k : Fin (2 * m)) : 0 < lenNat c m k.val := by
  have hk := k.isLt
  fin_cases c
  · exact len0_pos hm he hk
  · exact len1_pos hm he hk
  · exact len2_pos hm he hk

end SigFLemmas

/-! ## Heads, the straight walk and the generic traversal/coverage -/

section Generic

variable {m : Nat} [NeZero m]

/-- Head of interval `k`: one drift step after the seam point of rank
`k + 1`. -/
def headF (c : Fin 3) (m : Nat) [NeZero m] (k : Fin (2 * m)) :
    TerminalQ m :=
  seamPoint m c (seamSucc m k) + uVec m c

/-- The level-1 core map in pair coordinates. -/
def coreMap (c : Fin 3) (m : Nat) [NeZero m] (w : TerminalQ m) :
    TerminalQ m :=
  rho c w + uVec m c

/-- Straight walk along the drift ray while the orbit stays inactive. -/
private theorem walk_ray (hm : 4 ≤ m) (c : Fin 3) (x : TerminalQ m) :
    ∀ J : Nat, (∀ i, i < J → ¬ activePred c (x + i • uVec m c)) →
      (coreMap c m)^[J] x = x + J • uVec m c
  | 0, _ => by
      rw [Function.iterate_zero_apply, zero_nsmul, add_zero]
  | J + 1, h => by
      rw [Function.iterate_succ_apply',
        walk_ray hm c x J (fun i hi => h i (by omega))]
      show rho c (x + J • uVec m c) + uVec m c = _
      rw [rho_eq_of_not_active hm c (h J (by omega)), succ_nsmul,
        ← add_assoc]

/-- The per-color interval specification: all ray points before the first
hit are inactive, and the first hit is the seam point of rank `σ_c k`. -/
def SpecAt (c : Fin 3) (m : Nat) [NeZero m] (k : Fin (2 * m)) : Prop :=
  (∀ i, i < lenNat c m k.val - 1 →
      ¬ activePred c (headF c m k + i • uVec m c)) ∧
    headF c m k + (lenNat c m k.val - 1) • uVec m c
      = seamPoint m c (sigF c m k)

/-- Traversal from the interval specification: walk to the first active
point, then one `ρ_c` kick lands on the next head. -/
private theorem traverse_of_spec (hm : 8 ≤ m) (he : m % 2 = 0) (c : Fin 3)
    (hspec : ∀ k, SpecAt c m k) (k : Fin (2 * m)) :
    (coreMap c m)^[lenNat c m k.val] (headF c m k)
      = headF c m (sigF c m k) := by
  obtain ⟨hin, hhit⟩ := hspec k
  obtain ⟨J, hJ⟩ : ∃ J, lenNat c m k.val = J + 1 :=
    ⟨lenNat c m k.val - 1, by have := lenF_pos hm he c k; omega⟩
  have hJ' : lenNat c m k.val - 1 = J := by omega
  rw [hJ, Function.iterate_succ_apply',
    walk_ray (by omega) c _ J (by rw [← hJ']; exact hin)]
  rw [show (J : Nat) • uVec m c = (lenNat c m k.val - 1) • uVec m c by
    rw [hJ'], hhit]
  show rho c (seamPoint m c (sigF c m k)) + uVec m c = _
  rw [rho_seamPoint (by omega) c (sigF c m k)]
  rfl

private def decActive : (c : Fin 3) → (w : TerminalQ m) →
    Decidable (activePred c w)
  | 0, w => inferInstanceAs (Decidable (memP w ∨ memQ w))
  | 1, w => inferInstanceAs (Decidable (memP w ∨ memS w))
  | 2, w => inferInstanceAs (Decidable (memQ w ∨ memS w))

/-- Coverage from the interval specification: every point lies on the
interval owned by the label whose first hit is the first active point on
the forward drift ray from the point. -/
private theorem cover_of_spec (hm : 8 ≤ m) (he : m % 2 = 0) (c : Fin 3)
    (hspec : ∀ k, SpecAt c m k)
    (hσsurj : Function.Surjective (sigF c m))
    (hhit : ∀ w : TerminalQ m, ∃ j : Nat,
      activePred c (w + j • uVec m c))
    (w : TerminalQ m) :
    ∃ k : Fin (2 * m), ∃ j : Nat, j < lenNat c m k.val ∧
      (coreMap c m)^[j] (headF c m k) = w := by
  haveI : DecidablePred (fun j : Nat =>
      activePred c (w + j • uVec m c)) :=
    fun j => decActive c _
  have hex : ∃ j : Nat, activePred c (w + j • uVec m c) := hhit w
  have hj₀ := Nat.find_spec hex
  have hmin : ∀ i, i < Nat.find hex →
      ¬ activePred c (w + i • uVec m c) :=
    fun i hi => Nat.find_min hex hi
  set j₀ := Nat.find hex with hj₀def
  obtain ⟨n, hn⟩ :=
    (activePred_iff_exists (by omega : 4 ≤ m) c _).mp hj₀
  obtain ⟨k, hk⟩ := hσsurj n
  obtain ⟨hin, hhit'⟩ := hspec k
  set J := lenNat c m k.val - 1 with hJdef
  have hlen := lenF_pos hm he c k
  have hkey : headF c m k + J • uVec m c = w + j₀ • uVec m c := by
    rw [hhit', hk, hn]
  have hJle : j₀ ≤ J := by
    by_contra hgt'
    have hgt : J < j₀ := Nat.lt_of_not_le hgt'
    have hsplit : w + j₀ • uVec m c
        = (w + (j₀ - (J + 1)) • uVec m c) + (J + 1) • uVec m c := by
      rw [add_assoc, ← add_nsmul]
      congr 2
      omega
    have hhead : headF c m k + J • uVec m c
        = seamPoint m c (seamSucc m k) + (J + 1) • uVec m c := by
      show seamPoint m c (seamSucc m k) + uVec m c + J • uVec m c = _
      rw [add_assoc, succ_nsmul']
    have hcancel : seamPoint m c (seamSucc m k)
        = w + (j₀ - (J + 1)) • uVec m c := by
      have h2 := hkey
      rw [hhead, hsplit] at h2
      exact add_right_cancel h2
    exact hmin (j₀ - (J + 1)) (by omega)
      (by rw [← hcancel]; exact seamPoint_active (by omega) c _)
  refine ⟨k, J - j₀, by omega, ?_⟩
  have hw : headF c m k + (J - j₀) • uVec m c = w := by
    have hsplit : headF c m k + J • uVec m c
        = (headF c m k + (J - j₀) • uVec m c) + j₀ • uVec m c := by
      rw [add_assoc, ← add_nsmul]
      congr 2
      omega
    rw [hsplit] at hkey
    exact add_right_cancel hkey
  rw [walk_ray (by omega) c _ (J - j₀)
    (fun i hi => hin i (by omega)), hw]

end Generic

/-! ## Table evaluation lemmas -/

section TableEval

set_option maxHeartbeats 1600000 in
private theorem sig0_eq {m k v : Nat} (hm : 8 ≤ m) (he : m % 2 = 0)
    (h : (k ≤ m / 2 - 3 ∧ v = k + m / 2 + 1) ∨
      (k = m / 2 - 2 ∧ v = m / 2 - 1) ∨
      (m / 2 - 1 ≤ k ∧ k ≤ m - 3 ∧ v = 2 * k + 3) ∨
      (k = m - 2 ∧ v = 2 * m - 2) ∨ (k = m - 1 ∧ v = 2 * m - 1) ∨
      (k = m ∧ v = 0) ∨ (k = 2 * m - 3 ∧ v = m - 1) ∨
      (k = 2 * m - 2 ∧ v = m) ∨ (k = 2 * m - 1 ∧ v = m / 2) ∨
      (m + 1 ≤ k ∧ k ≤ 2 * m - 4 ∧ k % 2 = 1 ∧ v = k + 1) ∨
      (m + 2 ≤ k ∧ k ≤ 2 * m - 4 ∧ k % 2 = 0 ∧ v = (k - m) / 2)) :
    sig0 m k = v := by
  unfold sig0
  split_ifs <;> omega

set_option maxHeartbeats 1600000 in
private theorem len0_eq {m k v : Nat} (hm : 8 ≤ m) (he : m % 2 = 0)
    (h : (k ≤ m / 2 - 3 ∧ v = m / 2) ∨
      (k = m / 2 - 2 ∧ v = m) ∨
      (m / 2 - 1 ≤ k ∧ k ≤ m - 3 ∧ v = m - 2 - k) ∨
      (k = m - 2 ∧ v = 1) ∨ (k = m - 1 ∧ v = 1) ∨
      (k = m ∧ v = 1) ∨ (k = 2 * m - 3 ∧ v = m - 1) ∨
      (k = 2 * m - 2 ∧ v = m - 1) ∨ (k = 2 * m - 1 ∧ v = m / 2) ∨
      (m + 1 ≤ k ∧ k ≤ 2 * m - 4 ∧ k % 2 = 1 ∧ v = m) ∨
      (m + 2 ≤ k ∧ k ≤ 2 * m - 4 ∧ k % 2 = 0 ∧ v = (k - m) / 2 + 1)) :
    len0 m k = v := by
  unfold len0
  split_ifs <;> omega

set_option maxHeartbeats 1600000 in
private theorem sig1_eq {m k v : Nat} (hm : 8 ≤ m) (he : m % 2 = 0)
    (h : (k = 0 ∧ v = m + 2) ∨ (k = 1 ∧ v = m + 3) ∨
      (2 ≤ k ∧ k ≤ m / 2 ∧ v = k + m / 2 + 1) ∨
      (k = m / 2 + 1 ∧ v = m / 2 + 2) ∨
      (m / 2 + 2 ≤ k ∧ k ≤ m - 1 ∧ v = 2 * k) ∨
      (m ≤ k ∧ k ≤ m + 3 ∧ v = k - m) ∨
      (k = 2 * m - 1 ∧ v = m / 2 + 1) ∨
      (m + 4 ≤ k ∧ k ≤ 2 * m - 2 ∧ k % 2 = 0 ∧ v = k + 1) ∨
      (m + 5 ≤ k ∧ k ≤ 2 * m - 3 ∧ k % 2 = 1 ∧ v = (k - m + 3) / 2)) :
    sig1 m k = v := by
  unfold sig1
  split_ifs <;> omega

set_option maxHeartbeats 1600000 in
private theorem len1_eq {m k v : Nat} (hm : 8 ≤ m) (he : m % 2 = 0)
    (h : (k = 0 ∧ v = m - 1) ∨ (k = 1 ∧ v = m - 1) ∨
      (2 ≤ k ∧ k ≤ m / 2 ∧ v = m / 2) ∨
      (k = m / 2 + 1 ∧ v = m) ∨
      (m / 2 + 2 ≤ k ∧ k ≤ m - 1 ∧ v = m + 1 - k) ∨
      (m ≤ k ∧ k ≤ m + 3 ∧ v = 1) ∨
      (k = 2 * m - 1 ∧ v = m / 2 - 1) ∨
      (m + 4 ≤ k ∧ k ≤ 2 * m - 2 ∧ k % 2 = 0 ∧ v = m) ∨
      (m + 5 ≤ k ∧ k ≤ 2 * m - 3 ∧ k % 2 = 1 ∧ v = (k - m - 1) / 2)) :
    len1 m k = v := by
  unfold len1
  split_ifs <;> omega

set_option maxHeartbeats 1600000 in
private theorem sig2_eq {m k v : Nat} (hm : 8 ≤ m) (he : m % 2 = 0)
    (h : (k = 0 ∧ v = m) ∨
      (1 ≤ k ∧ k ≤ m - 4 ∧ k % 2 = 1 ∧ v = k + 1) ∨
      (2 ≤ k ∧ k ≤ m - 4 ∧ k % 2 = 0 ∧ v = k / 2 + m) ∨
      (k = m - 3 ∧ v = 2 * m - 1) ∨ (k = m - 2 ∧ v = 0) ∨
      (k = m - 1 ∧ v = m + m / 2) ∨
      (m ≤ k ∧ k ≤ m + m / 2 - 3 ∧ v = k + m / 2 + 1) ∨
      (k = m + m / 2 - 2 ∧ v = k + 1) ∨
      (m + m / 2 - 1 ≤ k ∧ k ≤ 2 * m - 3 ∧ v = 2 * k + 3 - 3 * m) ∨
      (k = 2 * m - 2 ∧ v = m - 2) ∨ (k = 2 * m - 1 ∧ v = m - 1)) :
    sig2 m k = v := by
  unfold sig2
  split_ifs <;> omega

set_option maxHeartbeats 1600000 in
private theorem len2_eq {m k v : Nat} (hm : 8 ≤ m) (he : m % 2 = 0)
    (h : (k = 0 ∧ v = 1) ∨
      (1 ≤ k ∧ k ≤ m - 4 ∧ k % 2 = 1 ∧ v = m) ∨
      (2 ≤ k ∧ k ≤ m - 4 ∧ k % 2 = 0 ∧ v = k / 2 + 1) ∨
      (k = m - 3 ∧ v = m - 1) ∨ (k = m - 2 ∧ v = m - 1) ∨
      (k = m - 1 ∧ v = m / 2) ∨
      (m ≤ k ∧ k ≤ m + m / 2 - 3 ∧ v = m / 2) ∨
      (k = m + m / 2 - 2 ∧ v = m) ∨
      (m + m / 2 - 1 ≤ k ∧ k ≤ 2 * m - 3 ∧ v = 2 * m - 2 - k) ∨
      (k = 2 * m - 2 ∧ v = 1) ∨ (k = 2 * m - 1 ∧ v = 1)) :
    len2 m k = v := by
  unfold len2
  split_ifs <;> omega

end TableEval

/-! ## The interval specifications, color by color -/

section Specs

set_option maxHeartbeats 1600000 in
private theorem spec0 {m : Nat} [NeZero m] (hm : 8 ≤ m) (he : m % 2 = 0)
    (k : Fin (2 * m)) : SpecAt 0 m k := by
  have hk := k.isLt
  have hm4 : 4 ≤ m := by omega
  by_cases hB1 : k.val ≤ m / 2 - 3
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 0 m k = (cpt (2 * m - k.val) (k.val + 2) : TerminalQ m) := by
      show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
      rw [hs, sp0_anti hm4 (by omega)]
      rw [show (uVec m 0 : TerminalQ m) = cpt 1 1 from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig0 m k.val = k.val + m / 2 + 1 :=
      sig0_eq hm he (Or.inl ⟨by omega, by omega⟩)
    have hlen : len0 m k.val = m / 2 :=
      len0_eq hm he (Or.inl ⟨by omega, by omega⟩)
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_zero, hlen] at hi
      rw [hhead, cpt_add_u0 hm4]
      intro hact
      have hval := active0_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 2 * m - k.val + i) (by omega)
      have hy := val_cases4m (m := m) (a := k.val + 2 + i) (by omega)
      omega
    · rw [lenNat_zero, hlen, hhead, cpt_add_u0 hm4]
      show _ = seamPoint0Nat m (sigF 0 m k).val
      rw [sigF_val hm he, sigNat_zero, hsig]
      rw [sp0_anti hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hB2 : k.val = m / 2 - 2
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 0 m k = (cpt (2 * m - k.val) (k.val + 2) : TerminalQ m) := by
      show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
      rw [hs, sp0_anti hm4 (by omega)]
      rw [show (uVec m 0 : TerminalQ m) = cpt 1 1 from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig0 m k.val = m / 2 - 1 :=
      sig0_eq hm he (Or.inr (Or.inl ⟨by omega, by omega⟩))
    have hlen : len0 m k.val = m :=
      len0_eq hm he (Or.inr (Or.inl ⟨by omega, by omega⟩))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_zero, hlen] at hi
      rw [hhead, cpt_add_u0 hm4]
      intro hact
      have hval := active0_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 2 * m - k.val + i) (by omega)
      have hy := val_cases4m (m := m) (a := k.val + 2 + i) (by omega)
      omega
    · rw [lenNat_zero, hlen, hhead, cpt_add_u0 hm4]
      show _ = seamPoint0Nat m (sigF 0 m k).val
      rw [sigF_val hm he, sigNat_zero, hsig]
      rw [sp0_anti hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hB3 : k.val ≤ m - 3
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 0 m k = (cpt (2 * m - k.val) (k.val + 2) : TerminalQ m) := by
      show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
      rw [hs, sp0_anti hm4 (by omega)]
      rw [show (uVec m 0 : TerminalQ m) = cpt 1 1 from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig0 m k.val = 2 * k.val + 3 :=
      sig0_eq hm he (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))
    have hlen : len0 m k.val = m - 2 - k.val :=
      len0_eq hm he (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_zero, hlen] at hi
      rw [hhead, cpt_add_u0 hm4]
      intro hact
      have hval := active0_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 2 * m - k.val + i) (by omega)
      have hy := val_cases4m (m := m) (a := k.val + 2 + i) (by omega)
      omega
    · rw [lenNat_zero, hlen, hhead, cpt_add_u0 hm4]
      show _ = seamPoint0Nat m (sigF 0 m k).val
      rw [sigF_val hm he, sigNat_zero, hsig]
      rw [sp0_row hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hB4 : k.val = m - 2
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 0 m k = (cpt (2) (m - 1) : TerminalQ m) := by
      show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
      rw [hs, sp0_mid hm4 (by omega)]
      rw [show (uVec m 0 : TerminalQ m) = cpt 1 1 from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig0 m k.val = 2 * m - 2 :=
      sig0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
    have hlen : len0 m k.val = 1 :=
      len0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_zero, hlen] at hi
      rw [hhead, cpt_add_u0 hm4]
      intro hact
      have hval := active0_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 2 + i) (by omega)
      have hy := val_cases4m (m := m) (a := m - 1 + i) (by omega)
      omega
    · rw [lenNat_zero, hlen, hhead, cpt_add_u0 hm4]
      show _ = seamPoint0Nat m (sigF 0 m k).val
      rw [sigF_val hm he, sigNat_zero, hsig]
      rw [sp0_rowEnd hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hB5 : k.val = m - 1
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 0 m k = (cpt (1) (0) : TerminalQ m) := by
      show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
      rw [hs, sp0_row hm4 (by omega) (by omega)]
      rw [show (uVec m 0 : TerminalQ m) = cpt 1 1 from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig0 m k.val = 2 * m - 1 :=
      sig0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))
    have hlen : len0 m k.val = 1 :=
      len0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_zero, hlen] at hi
      rw [hhead, cpt_add_u0 hm4]
      intro hact
      have hval := active0_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 1 + i) (by omega)
      have hy := val_cases4m (m := m) (a := 0 + i) (by omega)
      omega
    · rw [lenNat_zero, hlen, hhead, cpt_add_u0 hm4]
      show _ = seamPoint0Nat m (sigF 0 m k).val
      rw [sigF_val hm he, sigNat_zero, hsig]
      rw [sp0_last hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hB6 : k.val = m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 0 m k = (cpt (m) (m) : TerminalQ m) := by
      show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
      rw [hs, sp0_row hm4 (by omega) (by omega)]
      rw [show (uVec m 0 : TerminalQ m) = cpt 1 1 from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig0 m k.val = 0 :=
      sig0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))
    have hlen : len0 m k.val = 1 :=
      len0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_zero, hlen] at hi
      rw [hhead, cpt_add_u0 hm4]
      intro hact
      have hval := active0_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := m + i) (by omega)
      have hy := val_cases4m (m := m) (a := m + i) (by omega)
      omega
    · rw [lenNat_zero, hlen, hhead, cpt_add_u0 hm4]
      show _ = seamPoint0Nat m (sigF 0 m k).val
      rw [sigF_val hm he, sigNat_zero, hsig]
      rw [sp0_anti hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hB9 : k.val = 2 * m - 3
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 0 m k = (cpt (3) (0) : TerminalQ m) := by
      show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
      rw [hs, sp0_rowEnd hm4 (by omega)]
      rw [show (uVec m 0 : TerminalQ m) = cpt 1 1 from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig0 m k.val = m - 1 :=
      sig0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))))
    have hlen : len0 m k.val = m - 1 :=
      len0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_zero, hlen] at hi
      rw [hhead, cpt_add_u0 hm4]
      intro hact
      have hval := active0_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 3 + i) (by omega)
      have hy := val_cases4m (m := m) (a := 0 + i) (by omega)
      omega
    · rw [lenNat_zero, hlen, hhead, cpt_add_u0 hm4]
      show _ = seamPoint0Nat m (sigF 0 m k).val
      rw [sigF_val hm he, sigNat_zero, hsig]
      rw [sp0_mid hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hB10 : k.val = 2 * m - 2
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 0 m k = (cpt (2) (1) : TerminalQ m) := by
      show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
      rw [hs, sp0_last hm4 (by omega)]
      rw [show (uVec m 0 : TerminalQ m) = cpt 1 1 from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig0 m k.val = m :=
      sig0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))))
    have hlen : len0 m k.val = m - 1 :=
      len0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_zero, hlen] at hi
      rw [hhead, cpt_add_u0 hm4]
      intro hact
      have hval := active0_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 2 + i) (by omega)
      have hy := val_cases4m (m := m) (a := 1 + i) (by omega)
      omega
    · rw [lenNat_zero, hlen, hhead, cpt_add_u0 hm4]
      show _ = seamPoint0Nat m (sigF 0 m k).val
      rw [sigF_val hm he, sigNat_zero, hsig]
      rw [sp0_row hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hB11 : k.val = 2 * m - 1
  · have hs : (seamSucc m k).val = 0 := seamSucc_val_last (by omega)
    have hhead : headF 0 m k = (cpt (1) (1) : TerminalQ m) := by
      show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
      rw [hs, sp0_anti hm4 (by omega)]
      rw [show (uVec m 0 : TerminalQ m) = cpt 1 1 from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig0 m k.val = m / 2 :=
      sig0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))))))
    have hlen : len0 m k.val = m / 2 :=
      len0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_zero, hlen] at hi
      rw [hhead, cpt_add_u0 hm4]
      intro hact
      have hval := active0_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 1 + i) (by omega)
      have hy := val_cases4m (m := m) (a := 1 + i) (by omega)
      omega
    · rw [lenNat_zero, hlen, hhead, cpt_add_u0 hm4]
      show _ = seamPoint0Nat m (sigF 0 m k).val
      rw [sigF_val hm he, sigNat_zero, hsig]
      rw [sp0_anti hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hPar : k.val % 2 = 1
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 0 m k = (cpt (2 * m - k.val) (0) : TerminalQ m) := by
      show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
      rw [hs, sp0_row hm4 (by omega) (by omega)]
      rw [show (uVec m 0 : TerminalQ m) = cpt 1 1 from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig0 m k.val = k.val + 1 :=
      sig0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))))))))))
    have hlen : len0 m k.val = m :=
      len0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_zero, hlen] at hi
      rw [hhead, cpt_add_u0 hm4]
      intro hact
      have hval := active0_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 2 * m - k.val + i) (by omega)
      have hy := val_cases4m (m := m) (a := 0 + i) (by omega)
      omega
    · rw [lenNat_zero, hlen, hhead, cpt_add_u0 hm4]
      show _ = seamPoint0Nat m (sigF 0 m k).val
      rw [sigF_val hm he, sigNat_zero, hsig]
      rw [sp0_row hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  have hs : (seamSucc m k).val = k.val + 1 :=
    seamSucc_val_of_lt (by omega)
  have hhead : headF 0 m k = (cpt (2 * m - k.val) (0) : TerminalQ m) := by
    show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
    rw [hs, sp0_row hm4 (by omega) (by omega)]
    rw [show (uVec m 0 : TerminalQ m) = cpt 1 1 from rfl, cpt_add]
    all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  have hsig : sig0 m k.val = (k.val - m) / 2 :=
    sig0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega⟩)))))))))))
  have hlen : len0 m k.val = (k.val - m) / 2 + 1 :=
    len0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega⟩)))))))))))
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [lenNat_zero, hlen] at hi
    rw [hhead, cpt_add_u0 hm4]
    intro hact
    have hval := active0_cpt hm4 hact
    have hx := val_cases4m (m := m) (a := 2 * m - k.val + i) (by omega)
    have hy := val_cases4m (m := m) (a := 0 + i) (by omega)
    omega
  · rw [lenNat_zero, hlen, hhead, cpt_add_u0 hm4]
    show _ = seamPoint0Nat m (sigF 0 m k).val
    rw [sigF_val hm he, sigNat_zero, hsig]
    rw [sp0_anti hm4 (by omega)]
    all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))

set_option maxHeartbeats 1600000 in
private theorem spec1 {m : Nat} [NeZero m] (hm : 8 ≤ m) (he : m % 2 = 0)
    (k : Fin (2 * m)) : SpecAt 1 m k := by
  have hk := k.isLt
  have hm4 : 4 ≤ m := by omega
  by_cases hC1 : k.val = 0
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (2 * m - 1) (0) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_one hm4 (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt (2 * m - 2) 1 from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = m + 2 :=
      sig1_eq hm he (Or.inl ⟨by omega, by omega⟩)
    have hlen : len1 m k.val = m - 1 :=
      len1_eq hm he (Or.inl ⟨by omega, by omega⟩)
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm4 _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 2 * m - 1 + (2 * m - 2 * i)) (by omega)
      have hy := val_cases4m (m := m) (a := 0 + i) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead, cpt_add_u1 hm4 _ _ (m - 1 - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he, sigNat_one, hsig]
      rw [sp1_hop hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC2 : k.val = 1
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (2 * m - 1) (m - 1) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_two hm4 (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt (2 * m - 2) 1 from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = m + 3 :=
      sig1_eq hm he (Or.inr (Or.inl ⟨by omega, by omega⟩))
    have hlen : len1 m k.val = m - 1 :=
      len1_eq hm he (Or.inr (Or.inl ⟨by omega, by omega⟩))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm4 _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 2 * m - 1 + (2 * m - 2 * i)) (by omega)
      have hy := val_cases4m (m := m) (a := m - 1 + i) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead, cpt_add_u1 hm4 _ _ (m - 1 - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he, sigNat_one, hsig]
      rw [sp1_anti hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC3 : k.val ≤ m / 2
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (0) (2 * m - k.val) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_col hm4 (by omega) (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt (2 * m - 2) 1 from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = k.val + m / 2 + 1 :=
      sig1_eq hm he (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))
    have hlen : len1 m k.val = m / 2 :=
      len1_eq hm he (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm4 _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 0 + (2 * m - 2 * i)) (by omega)
      have hy := val_cases4m (m := m) (a := 2 * m - k.val + i) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead, cpt_add_u1 hm4 _ _ (m / 2 - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he, sigNat_one, hsig]
      by_cases hsub : k.val ≤ m / 2 - 1
      · rw [sp1_col hm4 (by omega) (by omega)]
        all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
      · rw [sp1_colEnd hm4 (by omega)]
        all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC4 : k.val = m / 2 + 1
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (0) (2 * m - k.val) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_col hm4 (by omega) (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt (2 * m - 2) 1 from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = m / 2 + 2 :=
      sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
    have hlen : len1 m k.val = m :=
      len1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm4 _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 0 + (2 * m - 2 * i)) (by omega)
      have hy := val_cases4m (m := m) (a := 2 * m - k.val + i) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead, cpt_add_u1 hm4 _ _ (m - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he, sigNat_one, hsig]
      rw [sp1_col hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC5 : k.val ≤ m - 1
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (0) (2 * m - k.val) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_col hm4 (by omega) (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt (2 * m - 2) 1 from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = 2 * k.val :=
      sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))
    have hlen : len1 m k.val = m + 1 - k.val :=
      len1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm4 _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 0 + (2 * m - 2 * i)) (by omega)
      have hy := val_cases4m (m := m) (a := 2 * m - k.val + i) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead, cpt_add_u1 hm4 _ _ (m + 1 - k.val - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he, sigNat_one, hsig]
      rw [sp1_anti hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC6 : k.val = m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (0) (0) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_colEnd hm4 (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt (2 * m - 2) 1 from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = 0 :=
      sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))
    have hlen : len1 m k.val = 1 :=
      len1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm4 _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 0 + (2 * m - 2 * i)) (by omega)
      have hy := val_cases4m (m := m) (a := 0 + i) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead, cpt_add_u1 hm4 _ _ (1 - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he, sigNat_one, hsig]
      rw [sp1_zero hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC7 : k.val = m + 1
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (1) (m - 1) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_hop hm4 (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt (2 * m - 2) 1 from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = 1 :=
      sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))
    have hlen : len1 m k.val = 1 :=
      len1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm4 _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 1 + (2 * m - 2 * i)) (by omega)
      have hy := val_cases4m (m := m) (a := m - 1 + i) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead, cpt_add_u1 hm4 _ _ (1 - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he, sigNat_one, hsig]
      rw [sp1_one hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC8 : k.val = m + 2
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (1) (m - 2) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_anti hm4 (by omega) (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt (2 * m - 2) 1 from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = 2 :=
      sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))
    have hlen : len1 m k.val = 1 :=
      len1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm4 _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 1 + (2 * m - 2 * i)) (by omega)
      have hy := val_cases4m (m := m) (a := m - 2 + i) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead, cpt_add_u1 hm4 _ _ (1 - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he, sigNat_one, hsig]
      rw [sp1_two hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC9 : k.val = m + 3
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (2) (m - 3) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_anti hm4 (by omega) (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt (2 * m - 2) 1 from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = 3 :=
      sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))
    have hlen : len1 m k.val = 1 :=
      len1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm4 _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 2 + (2 * m - 2 * i)) (by omega)
      have hy := val_cases4m (m := m) (a := m - 3 + i) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead, cpt_add_u1 hm4 _ _ (1 - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he, sigNat_one, hsig]
      rw [sp1_col hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC12 : k.val = 2 * m - 1
  · have hs : (seamSucc m k).val = 0 := seamSucc_val_last (by omega)
    have hhead : headF 1 m k = (cpt (2 * m - 2) (1) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_zero hm4 (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt (2 * m - 2) 1 from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = m / 2 + 1 :=
      sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))))
    have hlen : len1 m k.val = m / 2 - 1 :=
      len1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm4 _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 2 * m - 2 + (2 * m - 2 * i)) (by omega)
      have hy := val_cases4m (m := m) (a := 1 + i) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead, cpt_add_u1 hm4 _ _ (m / 2 - 1 - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he, sigNat_one, hsig]
      rw [sp1_col hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hPar : k.val % 2 = 0
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (k.val - m - 1) (2 * m - k.val) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_anti hm4 (by omega) (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt (2 * m - 2) 1 from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = k.val + 1 :=
      sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))))))))
    have hlen : len1 m k.val = m :=
      len1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm4 _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := k.val - m - 1 + (2 * m - 2 * i)) (by omega)
      have hy := val_cases4m (m := m) (a := 2 * m - k.val + i) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead, cpt_add_u1 hm4 _ _ (m - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he, sigNat_one, hsig]
      rw [sp1_anti hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  have hs : (seamSucc m k).val = k.val + 1 :=
    seamSucc_val_of_lt (by omega)
  have hhead : headF 1 m k = (cpt (k.val - m - 1) (2 * m - k.val) : TerminalQ m) := by
    show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
    rw [hs, sp1_anti hm4 (by omega) (by omega)]
    rw [show (uVec m 1 : TerminalQ m) = cpt (2 * m - 2) 1 from rfl, cpt_add]
    all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  have hsig : sig1 m k.val = (k.val - m + 3) / 2 :=
    sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega⟩)))))))))
  have hlen : len1 m k.val = (k.val - m - 1) / 2 :=
    len1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega⟩)))))))))
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [lenNat_one, hlen] at hi
    rw [hhead, cpt_add_u1 hm4 _ _ i (by omega)]
    intro hact
    have hval := active1_cpt hm4 hact
    have hx := val_cases4m (m := m) (a := k.val - m - 1 + (2 * m - 2 * i)) (by omega)
    have hy := val_cases4m (m := m) (a := 2 * m - k.val + i) (by omega)
    omega
  · rw [lenNat_one, hlen, hhead, cpt_add_u1 hm4 _ _ ((k.val - m - 1) / 2 - 1) (by omega)]
    show _ = seamPoint1Nat m (sigF 1 m k).val
    rw [sigF_val hm he, sigNat_one, hsig]
    rw [sp1_col hm4 (by omega) (by omega)]
    all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))

set_option maxHeartbeats 1600000 in
private theorem spec2 {m : Nat} [NeZero m] (hm : 8 ≤ m) (he : m % 2 = 0)
    (k : Fin (2 * m)) : SpecAt 2 m k := by
  have hk := k.isLt
  have hm4 : 4 ≤ m := by omega
  by_cases hD1 : k.val = 0
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k = (cpt (3) (2 * m - 1) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [hs, sp2_col hm4 (by omega)]
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 (2 * m - 2) from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = m :=
      sig2_eq hm he (Or.inl ⟨by omega, by omega⟩)
    have hlen : len2 m k.val = 1 :=
      len2_eq hm he (Or.inl ⟨by omega, by omega⟩)
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm4 _ _ i (by omega)]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 3 + i) (by omega)
      have hy := val_cases4m (m := m) (a := 2 * m - 1 + (2 * m - 2 * i)) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead, cpt_add_u2 hm4 _ _ (1 - 1) (by omega)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he, sigNat_two, hsig]
      rw [sp2_row hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hD23 : k.val ≤ m - 4
  · by_cases hPar : k.val % 2 = 1
    · have hs : (seamSucc m k).val = k.val + 1 :=
        seamSucc_val_of_lt (by omega)
      have hhead : headF 2 m k = (cpt (3) (k.val + m - 1) : TerminalQ m) := by
        show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
        rw [hs, sp2_col hm4 (by omega)]
        rw [show (uVec m 2 : TerminalQ m) = cpt 1 (2 * m - 2) from rfl, cpt_add]
        all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
      have hsig : sig2 m k.val = k.val + 1 :=
        sig2_eq hm he (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))
      have hlen : len2 m k.val = m :=
        len2_eq hm he (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))
      refine ⟨?_, ?_⟩
      · intro i hi
        rw [lenNat_two, hlen] at hi
        rw [hhead, cpt_add_u2 hm4 _ _ i (by omega)]
        intro hact
        have hval := active2_cpt hm4 hact
        have hx := val_cases4m (m := m) (a := 3 + i) (by omega)
        have hy := val_cases4m (m := m) (a := k.val + m - 1 + (2 * m - 2 * i)) (by omega)
        omega
      · rw [lenNat_two, hlen, hhead, cpt_add_u2 hm4 _ _ (m - 1) (by omega)]
        show _ = seamPoint2Nat m (sigF 2 m k).val
        rw [sigF_val hm he, sigNat_two, hsig]
        rw [sp2_col hm4 (by omega)]
        all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    · have hs : (seamSucc m k).val = k.val + 1 :=
        seamSucc_val_of_lt (by omega)
      have hhead : headF 2 m k = (cpt (3) (k.val + m - 1) : TerminalQ m) := by
        show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
        rw [hs, sp2_col hm4 (by omega)]
        rw [show (uVec m 2 : TerminalQ m) = cpt 1 (2 * m - 2) from rfl, cpt_add]
        all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
      have hsig : sig2 m k.val = k.val / 2 + m :=
        sig2_eq hm he (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)))
      have hlen : len2 m k.val = k.val / 2 + 1 :=
        len2_eq hm he (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)))
      refine ⟨?_, ?_⟩
      · intro i hi
        rw [lenNat_two, hlen] at hi
        rw [hhead, cpt_add_u2 hm4 _ _ i (by omega)]
        intro hact
        have hval := active2_cpt hm4 hact
        have hx := val_cases4m (m := m) (a := 3 + i) (by omega)
        have hy := val_cases4m (m := m) (a := k.val + m - 1 + (2 * m - 2 * i)) (by omega)
        omega
      · rw [lenNat_two, hlen, hhead, cpt_add_u2 hm4 _ _ (k.val / 2 + 1 - 1) (by omega)]
        show _ = seamPoint2Nat m (sigF 2 m k).val
        rw [sigF_val hm he, sigNat_two, hsig]
        rw [sp2_row hm4 (by omega) (by omega)]
        all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hD4 : k.val = m - 3
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k = (cpt (3) (m - 4) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [hs, sp2_col hm4 (by omega)]
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 (2 * m - 2) from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = 2 * m - 1 :=
      sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
    have hlen : len2 m k.val = m - 1 :=
      len2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm4 _ _ i (by omega)]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 3 + i) (by omega)
      have hy := val_cases4m (m := m) (a := m - 4 + (2 * m - 2 * i)) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead, cpt_add_u2 hm4 _ _ (m - 1 - 1) (by omega)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he, sigNat_two, hsig]
      rw [sp2_last hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hD5 : k.val = m - 2
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k = (cpt (4) (m - 4) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [hs, sp2_hop hm4 (by omega)]
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 (2 * m - 2) from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = 0 :=
      sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))
    have hlen : len2 m k.val = m - 1 :=
      len2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm4 _ _ i (by omega)]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 4 + i) (by omega)
      have hy := val_cases4m (m := m) (a := m - 4 + (2 * m - 2 * i)) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead, cpt_add_u2 hm4 _ _ (m - 1 - 1) (by omega)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he, sigNat_two, hsig]
      rw [sp2_col hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hD6 : k.val = m - 1
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k = (cpt (4) (m - 3) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [hs, sp2_row hm4 (by omega) (by omega)]
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 (2 * m - 2) from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = m + m / 2 :=
      sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))
    have hlen : len2 m k.val = m / 2 :=
      len2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm4 _ _ i (by omega)]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 4 + i) (by omega)
      have hy := val_cases4m (m := m) (a := m - 3 + (2 * m - 2 * i)) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead, cpt_add_u2 hm4 _ _ (m / 2 - 1) (by omega)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he, sigNat_two, hsig]
      rw [sp2_row hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hD7 : k.val ≤ m + m / 2 - 3
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k = (cpt (k.val + 5 - m) (m - 3) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [hs, sp2_row hm4 (by omega) (by omega)]
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 (2 * m - 2) from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = k.val + m / 2 + 1 :=
      sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))))
    have hlen : len2 m k.val = m / 2 :=
      len2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm4 _ _ i (by omega)]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := k.val + 5 - m + i) (by omega)
      have hy := val_cases4m (m := m) (a := m - 3 + (2 * m - 2 * i)) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead, cpt_add_u2 hm4 _ _ (m / 2 - 1) (by omega)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he, sigNat_two, hsig]
      by_cases hsub : k.val ≤ m + m / 2 - 5
      · rw [sp2_row hm4 (by omega) (by omega)]
        all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
      by_cases hsub2 : k.val = m + m / 2 - 4
      · rw [sp2_rowZero hm4 (by omega)]
        all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
      · rw [sp2_preLast hm4 (by omega)]
        all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hD8 : k.val = m + m / 2 - 2
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k = (cpt (k.val + 5 - m) (m - 3) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [hs, sp2_row hm4 (by omega) (by omega)]
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 (2 * m - 2) from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = k.val + 1 :=
      sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))))
    have hlen : len2 m k.val = m :=
      len2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm4 _ _ i (by omega)]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := k.val + 5 - m + i) (by omega)
      have hy := val_cases4m (m := m) (a := m - 3 + (2 * m - 2 * i)) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead, cpt_add_u2 hm4 _ _ (m - 1) (by omega)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he, sigNat_two, hsig]
      rw [sp2_row hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hD9 : k.val ≤ 2 * m - 3
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k
        = (cpt (k.val + 5 - m) (m - 3) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 (2 * m - 2) from rfl]
      by_cases hsub : k.val ≤ 2 * m - 5
      · rw [hs, sp2_row hm4 (by omega) (by omega), cpt_add]
        all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
      by_cases hsub2 : k.val = 2 * m - 4
      · rw [hs, sp2_rowZero hm4 (by omega), cpt_add]
        all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
      · rw [hs, sp2_preLast hm4 (by omega), cpt_add]
        all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = 2 * k.val + 3 - 3 * m :=
      sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))))))
    have hlen : len2 m k.val = 2 * m - 2 - k.val :=
      len2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm4 _ _ i (by omega)]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := k.val + 5 - m + i) (by omega)
      have hy := val_cases4m (m := m)
        (a := m - 3 + (2 * m - 2 * i)) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead,
        cpt_add_u2 hm4 _ _ (2 * m - 2 - k.val - 1) (by omega)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he, sigNat_two, hsig, sp2_col hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hD10 : k.val = 2 * m - 2
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k = (cpt (2) (2 * m - 2) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [hs, sp2_last hm4 (by omega)]
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 (2 * m - 2) from rfl, cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = m - 2 :=
      sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))))))
    have hlen : len2 m k.val = 1 :=
      len2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm4 _ _ i (by omega)]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m) (a := 2 + i) (by omega)
      have hy := val_cases4m (m := m) (a := 2 * m - 2 + (2 * m - 2 * i)) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead, cpt_add_u2 hm4 _ _ (1 - 1) (by omega)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he, sigNat_two, hsig]
      rw [sp2_col hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  have hs : (seamSucc m k).val = 0 := seamSucc_val_last (by omega)
  have hhead : headF 2 m k = (cpt (3) (2 * m - 2) : TerminalQ m) := by
    show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
    rw [hs, sp2_col hm4 (by omega)]
    rw [show (uVec m 2 : TerminalQ m) = cpt 1 (2 * m - 2) from rfl, cpt_add]
    all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  have hsig : sig2 m k.val = m - 1 :=
    sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩)))))))))))
  have hlen : len2 m k.val = 1 :=
    len2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩)))))))))))
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [lenNat_two, hlen] at hi
    rw [hhead, cpt_add_u2 hm4 _ _ i (by omega)]
    intro hact
    have hval := active2_cpt hm4 hact
    have hx := val_cases4m (m := m) (a := 3 + i) (by omega)
    have hy := val_cases4m (m := m) (a := 2 * m - 2 + (2 * m - 2 * i)) (by omega)
    omega
  · rw [lenNat_two, hlen, hhead, cpt_add_u2 hm4 _ _ (1 - 1) (by omega)]
    show _ = seamPoint2Nat m (sigF 2 m k).val
    rw [sigF_val hm he, sigNat_two, hsig]
    rw [sp2_hop hm4 (by omega)]
    all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))

end Specs

/-! ## Every drift ray meets the active seam -/

section RayHits

variable {m : Nat} [NeZero m]

private theorem memP_anti_cpt (hm : 4 ≤ m) {x y : Nat}
    (hsum : x + y = m ∨ x + y = 2 * m ∨ x + y = 3 * m)
    (hx : 3 ≤ ((x : Nat) : ZMod m).val) : memP (cpt x y : TerminalQ m) := by
  refine Or.inr (Or.inl ⟨?_, hx⟩)
  show ((x : Nat) : ZMod m) + ((y : Nat) : ZMod m) = 0
  rw [show ((x : Nat) : ZMod m) + ((y : Nat) : ZMod m)
      = ((x + y : Nat) : ZMod m) by push_cast; ring]
  rcases hsum with h | h | h
  · rw [castShift (b := 0) 1 (by omega)]
    exact Nat.cast_zero
  · rw [castShift (b := 0) 2 (by omega)]
    exact Nat.cast_zero
  · rw [castShift (b := 0) 3 (by omega)]
    exact Nat.cast_zero

private theorem memQ_row_cpt (hm : 4 ≤ m) {x y : Nat}
    (hy : ((y : Nat) : ZMod m).val = m - 1)
    (hx : ((x : Nat) : ZMod m).val = 0 ∨ 3 ≤ ((x : Nat) : ZMod m).val) :
    memQ (cpt x y : TerminalQ m) := by
  refine Or.inl ⟨?_, ?_⟩
  · show ((y : Nat) : ZMod m) = -1
    have h2 : (((m - 1 : Nat)) : ZMod m).val = m - 1 := valNat_lt (by omega)
    exact (ZMod.val_injective m (hy.trans h2.symm)).trans
      (neg_one_cast hm).symm
  · rcases hx with h | h
    · exact Or.inl ((ZMod.val_eq_zero _).mp h)
    · exact Or.inr h

private theorem memS_col_cpt (hm : 4 ≤ m) {x y : Nat}
    (hx : ((x : Nat) : ZMod m) = ((2 : Nat) : ZMod m))
    (hy : ((y : Nat) : ZMod m).val ≤ m - 3) :
    memS (cpt x y : TerminalQ m) := by
  refine Or.inl ⟨?_, hy⟩
  show ((x : Nat) : ZMod m) = 2
  rw [hx]
  push_cast
  ring

private theorem exists_cpt_rep (w : TerminalQ m) :
    ∃ a b : Nat, a < m ∧ b < m ∧ w = cpt a b :=
  ⟨w.1.val, w.2.val, ZMod.val_lt w.1, ZMod.val_lt w.2, by
    unfold cpt
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]⟩

/-- Color 0 (`u₀ = (1,1)`): ride to the row `y = −1`; the only inactive
landing `x = 1` is fixed by riding `m/2` further onto the anti-diagonal. -/
private theorem hit0 {m : Nat} [NeZero m] (hm : 8 ≤ m) (he : m % 2 = 0)
    (w : TerminalQ m) : ∃ j : Nat, activePred 0 (w + j • uVec m 0) := by
  have hm4 : 4 ≤ m := by omega
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_cpt_rep w
  have hx1 := val_cases4m (m := m) (a := a + (m - 1 - b)) (by omega)
  by_cases h2 : ((a + (m - 1 - b) : Nat) : ZMod m).val = 2
  · refine ⟨m - 1 - b, ?_⟩
    rw [cpt_add_u0 hm4]
    refine Or.inl (Or.inr (Or.inr (Or.inr ?_)))
    show (cpt (a + (m - 1 - b)) (b + (m - 1 - b)) : TerminalQ m) = (2, -1)
    unfold cpt
    rw [Prod.mk.injEq]
    constructor
    · have hv2 : (((2 : Nat)) : ZMod m).val = 2 := valNat_lt (by omega)
      have h3 := ZMod.val_injective m (h2.trans hv2.symm)
      rw [h3]
      push_cast
      ring
    · rw [show b + (m - 1 - b) = m - 1 by omega]
      exact (neg_one_cast hm4).symm
  by_cases h1 : ((a + (m - 1 - b) : Nat) : ZMod m).val = 1
  · refine ⟨m - 1 - b + m / 2, ?_⟩
    rw [cpt_add_u0 hm4]
    have hx2 := val_cases4m (m := m)
      (a := a + (m - 1 - b + m / 2)) (by omega)
    exact Or.inl (memP_anti_cpt hm4 (by omega) (by omega))
  · refine ⟨m - 1 - b, ?_⟩
    rw [cpt_add_u0 hm4]
    refine Or.inr (memQ_row_cpt hm4 ?_ ?_)
    · rw [show b + (m - 1 - b) = m - 1 by omega]
      exact valNat_lt (by omega)
    · omega

/-- Color 1 (`u₁ = (−2,1)`): odd abscissas ride onto the `P` anti-diagonal
(or its `S` patch `(1,−1)`), even abscissas ride onto the `S` column
`x = 2`, dodging its two missing cells by half a period. -/
private theorem hit1 {m : Nat} [NeZero m] (hm : 8 ≤ m) (he : m % 2 = 0)
    (w : TerminalQ m) : ∃ j : Nat, activePred 1 (w + j • uVec m 1) := by
  have hm4 : 4 ≤ m := by omega
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_cpt_rep w
  by_cases hpar : a % 2 = 1
  · -- odd abscissa: ride to the anti-diagonal
    refine ⟨if a + b ≤ m then a + b else a + b - m, ?_⟩
    set j := if a + b ≤ m then a + b else a + b - m with hjdef
    have hj : j ≤ m ∧ (a + b = j ∨ a + b = j + m) := by
      rw [hjdef]
      split_ifs <;> omega
    have hsum : a + (2 * m - 2 * j) + (b + j) = m
        ∨ a + (2 * m - 2 * j) + (b + j) = 2 * m
        ∨ a + (2 * m - 2 * j) + (b + j) = 3 * m := by
      omega
    rw [cpt_add_u1 hm4 _ _ j hj.1]
    have hxv := val_cases4m (m := m) (a := a + (2 * m - 2 * j)) (by omega)
    by_cases hX1 : ((a + (2 * m - 2 * j) : Nat) : ZMod m).val = 1
    · -- the landing is the `S` patch `(1, −1)`
      refine Or.inr (Or.inr (Or.inl ?_))
      show (cpt (a + (2 * m - 2 * j)) (b + j) : TerminalQ m) = (1, -1)
      unfold cpt
      rw [Prod.mk.injEq]
      have hv1 : (((1 : Nat)) : ZMod m).val = 1 := valNat_lt (by omega)
      have hX : ((a + (2 * m - 2 * j) : Nat) : ZMod m)
          = ((1 : Nat) : ZMod m) :=
        ZMod.val_injective m (hX1.trans hv1.symm)
      constructor
      · rw [hX]
        push_cast
        ring
      · have h0 : ((a + (2 * m - 2 * j) : Nat) : ZMod m)
            + ((b + j : Nat) : ZMod m) = 0 := by
          rw [show ((a + (2 * m - 2 * j) : Nat) : ZMod m)
              + ((b + j : Nat) : ZMod m)
              = ((a + (2 * m - 2 * j) + (b + j) : Nat) : ZMod m)
            by push_cast; ring]
          rcases hsum with h | h | h
          · rw [castShift (b := 0) 1 (by omega)]
            exact Nat.cast_zero
          · rw [castShift (b := 0) 2 (by omega)]
            exact Nat.cast_zero
          · rw [castShift (b := 0) 3 (by omega)]
            exact Nat.cast_zero
        have h1c : ((1 : Nat) : ZMod m) = (1 : ZMod m) := Nat.cast_one
        linear_combination h0 - hX - h1c
    · exact Or.inl (memP_anti_cpt hm4 hsum (by omega))
  · -- even abscissa: ride onto the `S` column `x = 2`
    have hyv := val_cases4m (m := m)
      (a := b + (a + m - 2) / 2) (by omega)
    by_cases hbad : ((b + (a + m - 2) / 2 : Nat) : ZMod m).val ≤ m - 3
    · refine ⟨(a + m - 2) / 2, ?_⟩
      rw [cpt_add_u1 hm4 _ _ ((a + m - 2) / 2) (by omega)]
      refine Or.inr (memS_col_cpt hm4 ?_ hbad)
      rw [show a + (2 * m - 2 * ((a + m - 2) / 2)) = 2 + m by omega]
      exact castShift (b := 2) 1 (by omega)
    · -- dodge: the half-period shift lands at depth `≤ m − 3`
      by_cases h0 : a = 0
      · refine ⟨m - 1, ?_⟩
        rw [cpt_add_u1 hm4 _ _ (m - 1) (by omega)]
        have hyv2 := val_cases4m (m := m) (a := b + (m - 1)) (by omega)
        refine Or.inr (memS_col_cpt hm4 ?_ (by omega))
        rw [show a + (2 * m - 2 * (m - 1)) = a + 2 by omega,
          show a + 2 = 2 by omega]
      · refine ⟨(a - 2) / 2, ?_⟩
        rw [cpt_add_u1 hm4 _ _ ((a - 2) / 2) (by omega)]
        have hyv2 := val_cases4m (m := m)
          (a := b + (a - 2) / 2) (by omega)
        refine Or.inr (memS_col_cpt hm4 ?_ (by omega))
        rw [show a + (2 * m - 2 * ((a - 2) / 2)) = 2 + 2 * m by omega]
        exact castShift (b := 2) 2 (by omega)

/-- Color 2 (`u₂ = (1,−2)`): odd ordinates ride onto the `Q` row `y = −1`
(dodging its two missing cells by half a period), even ordinates onto the
`S` column `x = 2` (whose only even missing depth is the `Q` patch
`(2,−2)`). -/
private theorem hit2 {m : Nat} [NeZero m] (hm : 8 ≤ m) (he : m % 2 = 0)
    (w : TerminalQ m) : ∃ j : Nat, activePred 2 (w + j • uVec m 2) := by
  have hm4 : 4 ≤ m := by omega
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_cpt_rep w
  by_cases hpar : b % 2 = 1
  · -- odd ordinate: ride to the row `y = −1`
    have hxv := val_cases4m (m := m) (a := a + (b + 1) / 2) (by omega)
    by_cases hbad : ((a + (b + 1) / 2 : Nat) : ZMod m).val = 1
        ∨ ((a + (b + 1) / 2 : Nat) : ZMod m).val = 2
    · refine ⟨(b + 1) / 2 + m / 2, ?_⟩
      rw [cpt_add_u2 hm4 _ _ ((b + 1) / 2 + m / 2) (by omega)]
      have hxv2 := val_cases4m (m := m)
        (a := a + ((b + 1) / 2 + m / 2)) (by omega)
      refine Or.inl (memQ_row_cpt hm4 ?_ (by omega))
      rw [show b + (2 * m - 2 * ((b + 1) / 2 + m / 2)) = m - 1 by omega]
      exact valNat_lt (by omega)
    · refine ⟨(b + 1) / 2, ?_⟩
      rw [cpt_add_u2 hm4 _ _ ((b + 1) / 2) (by omega)]
      refine Or.inl (memQ_row_cpt hm4 ?_ (by omega))
      rw [show b + (2 * m - 2 * ((b + 1) / 2)) = 2 * m - 1 by omega,
        castShift (a := 2 * m - 1) (b := m - 1) 1 (by omega)]
      exact valNat_lt (by omega)
  · -- even ordinate: ride onto the `S` column `x = 2`
    refine ⟨if a ≤ 2 then 2 - a else 2 + m - a, ?_⟩
    set j := if a ≤ 2 then 2 - a else 2 + m - a with hjdef
    have hj : (a + j = 2 ∨ a + j = 2 + m) ∧ j ≤ m := by
      rw [hjdef]
      split_ifs <;> omega
    have hyv := val_cases4m (m := m)
      (a := b + (2 * m - 2 * j)) (by omega)
    rw [cpt_add_u2 hm4 _ _ j hj.2]
    by_cases hbad : ((b + (2 * m - 2 * j) : Nat) : ZMod m).val = m - 2
    · -- the landing is the `Q` patch `(2, −2)`
      refine Or.inl (Or.inr (Or.inr ?_))
      show (cpt (a + j) (b + (2 * m - 2 * j)) : TerminalQ m) = (2, -2)
      unfold cpt
      rw [Prod.mk.injEq]
      constructor
      · rcases hj.1 with h | h
        · rw [h]
          push_cast
          ring
        · rw [h, castShift (a := 2 + m) (b := 2) 1 (by omega)]
          push_cast
          ring
      · have hv2 : (((m - 2 : Nat)) : ZMod m).val = m - 2 :=
          valNat_lt (by omega)
        exact (ZMod.val_injective m (hbad.trans hv2.symm)).trans
          (neg_two_cast hm4).symm
    · refine Or.inr (memS_col_cpt hm4 ?_ (by omega))
      rcases hj.1 with h | h
      · rw [h]
      · rw [h]
        exact castShift (b := 2) 1 (by omega)

end RayHits

/-! ## Level 2: the label successor is a single `2m`-cycle

`σ_c` is spliced along the `m/2`-element transversal `ι_c` with constant
interval length `4`: four `σ_c`-steps advance the transversal index by `3`,
and `+3` generates `ZMod (m/2)` exactly because `3 ∤ m`. -/

section LevelTwo

/-- Level-2 transversal core. -/
def iotaNat (c : Fin 3) (m s : Nat) : Nat :=
  if c = 0 then (if s ≤ m / 2 - 2 then s else 2 * m - 1)
  else if c = 1 then (if s ≤ 1 then s else m + 2 * s)
  else (if s ≤ m / 2 - 2 then 2 * s else 2 * m - 1)

/-- Level-2 transversal: the `m/2` interval heads on the label circle. -/
def iota (c : Fin 3) (m : Nat) [NeZero (m / 2)] (t : ZMod (m / 2)) :
    Fin (2 * m) :=
  ⟨iotaNat c m t.val % (2 * m), Nat.mod_lt _ (by
    have h1 : 0 < m / 2 := Nat.pos_of_ne_zero (NeZero.ne _)
    omega)⟩

private theorem iotaNat_zero (m s : Nat) :
    iotaNat 0 m s = if s ≤ m / 2 - 2 then s else 2 * m - 1 := rfl

private theorem iotaNat_one (m s : Nat) :
    iotaNat 1 m s = if s ≤ 1 then s else m + 2 * s := rfl

private theorem iotaNat_two (m s : Nat) :
    iotaNat 2 m s = if s ≤ m / 2 - 2 then 2 * s else 2 * m - 1 := rfl

private theorem iota0_eq {m s v : Nat} (hm : 8 ≤ m)
    (h : (s ≤ m / 2 - 2 ∧ v = s) ∨ (m / 2 - 2 < s ∧ v = 2 * m - 1)) :
    iotaNat 0 m s = v := by
  rw [iotaNat_zero]
  split_ifs <;> omega

private theorem iota1_eq {m s v : Nat} (hm : 8 ≤ m)
    (h : (s ≤ 1 ∧ v = s) ∨ (2 ≤ s ∧ v = m + 2 * s)) :
    iotaNat 1 m s = v := by
  rw [iotaNat_one]
  split_ifs <;> omega

private theorem iota2_eq {m s v : Nat} (hm : 8 ≤ m)
    (h : (s ≤ m / 2 - 2 ∧ v = 2 * s) ∨ (m / 2 - 2 < s ∧ v = 2 * m - 1)) :
    iotaNat 2 m s = v := by
  rw [iotaNat_two]
  split_ifs <;> omega

private theorem iota_val {m : Nat} [NeZero (m / 2)] (hm : 8 ≤ m)
    {c : Fin 3} {t : ZMod (m / 2)} :
    (iota c m t).val = iotaNat c m t.val := by
  have hts := ZMod.val_lt t
  refine Nat.mod_eq_of_lt ?_
  rcases fin3_cases c with rfl | rfl | rfl
  · rw [iotaNat_zero]
    split_ifs <;> omega
  · rw [iotaNat_one]
    split_ifs <;> omega
  · rw [iotaNat_two]
    split_ifs <;> omega

/-- Value of the transversal index after the `+3` step. -/
private theorem val_add3 {m : Nat} [NeZero (m / 2)] (hm : 8 ≤ m)
    (t : ZMod (m / 2)) :
    ((t + 3).val = t.val + 3 ∧ t.val + 3 < m / 2) ∨
      ((t + 3).val = t.val + 3 - m / 2 ∧ m / 2 ≤ t.val + 3) := by
  have hts := ZMod.val_lt t
  have hcast : t + 3 = ((t.val + 3 : Nat) : ZMod (m / 2)) := by
    rw [show ((t.val + 3 : Nat) : ZMod (m / 2))
        = ((t.val : Nat) : ZMod (m / 2)) + 3 by push_cast; ring,
      ZMod.natCast_zmod_val]
  rcases Nat.lt_or_ge (t.val + 3) (m / 2) with hlt | hge
  · exact Or.inl ⟨by rw [hcast]; exact ZMod.val_natCast_of_lt hlt, hlt⟩
  · refine Or.inr ⟨?_, hge⟩
    rw [hcast, ZMod.val_natCast, Nat.mod_eq_sub_mod hge,
      Nat.mod_eq_of_lt (by omega)]

private theorem addThree_iterate {n : Nat} [NeZero n] (x : ZMod n) :
    ∀ j : Nat, (fun z : ZMod n => z + 3)^[j] x = x + (j : Nat) * 3
  | 0 => by
      rw [Function.iterate_zero_apply, Nat.cast_zero, zero_mul, add_zero]
  | j + 1 => by
      rw [Function.iterate_succ_apply', addThree_iterate x j]
      show x + (j : Nat) * 3 + 3 = _
      push_cast
      ring

/-- `+3` is a single cycle on `ZMod n` when `gcd(3, n) = 1` — the source of
the `3 ∤ m` hypothesis. -/
private theorem addThree_singleCycle (n : Nat) [NeZero n]
    (hcop : Nat.Coprime 3 n) :
    IsSingleCycleMap (fun z : ZMod n => z + 3) := by
  refine ⟨(Equiv.addRight (3 : ZMod n)).bijective, ?_⟩
  intro x y
  refine ⟨((y - x) * (((ZMod.unitOfCoprime 3 hcop)⁻¹ : (ZMod n)ˣ) :
    ZMod n)).val, ?_⟩
  rw [addThree_iterate, ZMod.natCast_zmod_val]
  have hcoe : ((ZMod.unitOfCoprime 3 hcop : (ZMod n)ˣ) : ZMod n) = 3 := by
    rw [ZMod.coe_unitOfCoprime]
    push_cast
    ring
  have hinv : (((ZMod.unitOfCoprime 3 hcop)⁻¹ : (ZMod n)ˣ) : ZMod n) * 3
      = 1 := by
    rw [← hcoe, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc x + (y - x) * (((ZMod.unitOfCoprime 3 hcop)⁻¹ : (ZMod n)ˣ) :
        ZMod n) * 3
      = x + (y - x) * ((((ZMod.unitOfCoprime 3 hcop)⁻¹ : (ZMod n)ˣ) :
          ZMod n) * 3) := by ring
    _ = y := by rw [hinv]; ring

end LevelTwo

set_option maxHeartbeats 1600000 in
private theorem chain0 {m : Nat} [NeZero m] [NeZero (m / 2)]
    (hm : 8 ≤ m) (he : m % 2 = 0) (t : ZMod (m / 2)) :
    (sigF 0 m)^[4] (iota 0 m t) = iota 0 m (t + 3) := by
  have hts := ZMod.val_lt t
  have ht3 := val_add3 hm t
  have hiter : (sigF 0 m)^[4] (iota 0 m t)
      = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))) :=
    rfl
  by_cases hc : t.val + 5 ≤ m / 2
  · have h10c1 : t.val ≤ m / 2 - 2 := by omega
    have h10v : t.val = t.val := by
      omega
    have v0 : (iota 0 m t).val = t.val := by
      rw [iota_val hm]
      exact iota0_eq hm (Or.inl ⟨h10c1, h10v⟩)
    have h11c1 : t.val ≤ m / 2 - 3 := by omega
    have h11v : t.val + m / 2 + 1 = t.val + m / 2 + 1 := by
      omega
    have v1 : (sigF 0 m (iota 0 m t)).val
        = t.val + m / 2 + 1 := by
      rw [sigF_val hm he, sigNat_zero, v0]
      exact sig0_eq hm he (Or.inl ⟨h11c1, h11v⟩)
    have h12c1 : m / 2 - 1 ≤ (t.val + m / 2 + 1) := by omega
    have h12c2 : (t.val + m / 2 + 1) ≤ m - 3 := by omega
    have h12v : 2 * t.val + m + 5 = 2 * (t.val + m / 2 + 1) + 3 := by
      omega
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m t))).val
        = 2 * t.val + m + 5 := by
      rw [sigF_val hm he, sigNat_zero, v1]
      exact sig0_eq hm he (Or.inr (Or.inr (Or.inl ⟨h12c1, h12c2, h12v⟩)))
    have h13c1 : m + 1 ≤ (2 * t.val + m + 5) := by omega
    have h13c2 : (2 * t.val + m + 5) ≤ 2 * m - 4 := by omega
    have h13c3 : (2 * t.val + m + 5) % 2 = 1 := by omega
    have h13v : 2 * t.val + m + 6 = (2 * t.val + m + 5) + 1 := by
      omega
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))).val
        = 2 * t.val + m + 6 := by
      rw [sigF_val hm he, sigNat_zero, v2]
      exact sig0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h13c1, h13c2, h13c3, h13v⟩))))))))))
    have h14c1 : m + 2 ≤ (2 * t.val + m + 6) := by omega
    have h14c2 : (2 * t.val + m + 6) ≤ 2 * m - 4 := by omega
    have h14c3 : (2 * t.val + m + 6) % 2 = 0 := by omega
    have h14v : t.val + 3 = ((2 * t.val + m + 6) - m) / 2 := by
      omega
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t))))).val
        = t.val + 3 := by
      rw [sigF_val hm he, sigNat_zero, v3]
      exact sig0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h14c1, h14c2, h14c3, h14v⟩)))))))))))
    have h1fc1 : (t + 3).val ≤ m / 2 - 2 := by omega
    have h1fv : t.val + 3 = (t + 3).val := by
      omega
    refine Fin.ext ?_
    rw [hiter, v4, iota_val hm]
    symm
    exact iota0_eq hm (Or.inl ⟨h1fc1, h1fv⟩)
  by_cases hc : t.val = m / 2 - 4
  · have h20c1 : t.val ≤ m / 2 - 2 := by omega
    have h20v : t.val = t.val := by
      omega
    have v0 : (iota 0 m t).val = t.val := by
      rw [iota_val hm]
      exact iota0_eq hm (Or.inl ⟨h20c1, h20v⟩)
    have h21c1 : t.val ≤ m / 2 - 3 := by omega
    have h21v : m - 3 = t.val + m / 2 + 1 := by
      omega
    have v1 : (sigF 0 m (iota 0 m t)).val
        = m - 3 := by
      rw [sigF_val hm he, sigNat_zero, v0]
      exact sig0_eq hm he (Or.inl ⟨h21c1, h21v⟩)
    have h22c1 : m / 2 - 1 ≤ (m - 3) := by omega
    have h22c2 : (m - 3) ≤ m - 3 := by omega
    have h22v : 2 * m - 3 = 2 * (m - 3) + 3 := by
      omega
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m t))).val
        = 2 * m - 3 := by
      rw [sigF_val hm he, sigNat_zero, v1]
      exact sig0_eq hm he (Or.inr (Or.inr (Or.inl ⟨h22c1, h22c2, h22v⟩)))
    have h23c1 : (2 * m - 3) = 2 * m - 3 := by omega
    have h23v : m - 1 = m - 1 := by
      omega
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))).val
        = m - 1 := by
      rw [sigF_val hm he, sigNat_zero, v2]
      exact sig0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h23c1, h23v⟩)))))))
    have h24c1 : (m - 1) = m - 1 := by omega
    have h24v : 2 * m - 1 = 2 * m - 1 := by
      omega
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t))))).val
        = 2 * m - 1 := by
      rw [sigF_val hm he, sigNat_zero, v3]
      exact sig0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h24c1, h24v⟩)))))
    have h2fc1 : m / 2 - 2 < (t + 3).val := by omega
    have h2fv : 2 * m - 1 = 2 * m - 1 := by
      omega
    refine Fin.ext ?_
    rw [hiter, v4, iota_val hm]
    symm
    exact iota0_eq hm (Or.inr (⟨h2fc1, h2fv⟩))
  by_cases hc : t.val = m / 2 - 3
  · have h30c1 : t.val ≤ m / 2 - 2 := by omega
    have h30v : t.val = t.val := by
      omega
    have v0 : (iota 0 m t).val = t.val := by
      rw [iota_val hm]
      exact iota0_eq hm (Or.inl ⟨h30c1, h30v⟩)
    have h31c1 : t.val ≤ m / 2 - 3 := by omega
    have h31v : m - 2 = t.val + m / 2 + 1 := by
      omega
    have v1 : (sigF 0 m (iota 0 m t)).val
        = m - 2 := by
      rw [sigF_val hm he, sigNat_zero, v0]
      exact sig0_eq hm he (Or.inl ⟨h31c1, h31v⟩)
    have h32c1 : (m - 2) = m - 2 := by omega
    have h32v : 2 * m - 2 = 2 * m - 2 := by
      omega
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m t))).val
        = 2 * m - 2 := by
      rw [sigF_val hm he, sigNat_zero, v1]
      exact sig0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inl ⟨h32c1, h32v⟩))))
    have h33c1 : (2 * m - 2) = 2 * m - 2 := by omega
    have h33v : m = m := by
      omega
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))).val
        = m := by
      rw [sigF_val hm he, sigNat_zero, v2]
      exact sig0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h33c1, h33v⟩))))))))
    have h34c1 : m = m := by omega
    have h34v : 0 = 0 := by
      omega
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t))))).val
        = 0 := by
      rw [sigF_val hm he, sigNat_zero, v3]
      exact sig0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h34c1, h34v⟩))))))
    have h3fc1 : (t + 3).val ≤ m / 2 - 2 := by omega
    have h3fv : 0 = (t + 3).val := by
      omega
    refine Fin.ext ?_
    rw [hiter, v4, iota_val hm]
    symm
    exact iota0_eq hm (Or.inl ⟨h3fc1, h3fv⟩)
  by_cases hc : t.val = m / 2 - 2
  · have h40c1 : t.val ≤ m / 2 - 2 := by omega
    have h40v : t.val = t.val := by
      omega
    have v0 : (iota 0 m t).val = t.val := by
      rw [iota_val hm]
      exact iota0_eq hm (Or.inl ⟨h40c1, h40v⟩)
    have h41c1 : t.val = m / 2 - 2 := by omega
    have h41v : m / 2 - 1 = m / 2 - 1 := by
      omega
    have v1 : (sigF 0 m (iota 0 m t)).val
        = m / 2 - 1 := by
      rw [sigF_val hm he, sigNat_zero, v0]
      exact sig0_eq hm he (Or.inr (Or.inl ⟨h41c1, h41v⟩))
    have h42c1 : m / 2 - 1 ≤ (m / 2 - 1) := by omega
    have h42c2 : (m / 2 - 1) ≤ m - 3 := by omega
    have h42v : m + 1 = 2 * (m / 2 - 1) + 3 := by
      omega
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m t))).val
        = m + 1 := by
      rw [sigF_val hm he, sigNat_zero, v1]
      exact sig0_eq hm he (Or.inr (Or.inr (Or.inl ⟨h42c1, h42c2, h42v⟩)))
    have h43c1 : m + 1 ≤ (m + 1) := by omega
    have h43c2 : (m + 1) ≤ 2 * m - 4 := by omega
    have h43c3 : (m + 1) % 2 = 1 := by omega
    have h43v : m + 2 = (m + 1) + 1 := by
      omega
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))).val
        = m + 2 := by
      rw [sigF_val hm he, sigNat_zero, v2]
      exact sig0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h43c1, h43c2, h43c3, h43v⟩))))))))))
    have h44c1 : m + 2 ≤ (m + 2) := by omega
    have h44c2 : (m + 2) ≤ 2 * m - 4 := by omega
    have h44c3 : (m + 2) % 2 = 0 := by omega
    have h44v : 1 = ((m + 2) - m) / 2 := by
      omega
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t))))).val
        = 1 := by
      rw [sigF_val hm he, sigNat_zero, v3]
      exact sig0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h44c1, h44c2, h44c3, h44v⟩)))))))))))
    have h4fc1 : (t + 3).val ≤ m / 2 - 2 := by omega
    have h4fv : 1 = (t + 3).val := by
      omega
    refine Fin.ext ?_
    rw [hiter, v4, iota_val hm]
    symm
    exact iota0_eq hm (Or.inl ⟨h4fc1, h4fv⟩)
  have h50c1 : m / 2 - 2 < t.val := by omega
  have h50v : 2 * m - 1 = 2 * m - 1 := by
    omega
  have v0 : (iota 0 m t).val = 2 * m - 1 := by
    rw [iota_val hm]
    exact iota0_eq hm (Or.inr (⟨h50c1, h50v⟩))
  have h51c1 : (2 * m - 1) = 2 * m - 1 := by omega
  have h51v : m / 2 = m / 2 := by
    omega
  have v1 : (sigF 0 m (iota 0 m t)).val
      = m / 2 := by
    rw [sigF_val hm he, sigNat_zero, v0]
    exact sig0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h51c1, h51v⟩)))))))))
  have h52c1 : m / 2 - 1 ≤ (m / 2) := by omega
  have h52c2 : (m / 2) ≤ m - 3 := by omega
  have h52v : m + 3 = 2 * (m / 2) + 3 := by
    omega
  have v2 : (sigF 0 m (sigF 0 m (iota 0 m t))).val
      = m + 3 := by
    rw [sigF_val hm he, sigNat_zero, v1]
    exact sig0_eq hm he (Or.inr (Or.inr (Or.inl ⟨h52c1, h52c2, h52v⟩)))
  have h53c1 : m + 1 ≤ (m + 3) := by omega
  have h53c2 : (m + 3) ≤ 2 * m - 4 := by omega
  have h53c3 : (m + 3) % 2 = 1 := by omega
  have h53v : m + 4 = (m + 3) + 1 := by
    omega
  have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))).val
      = m + 4 := by
    rw [sigF_val hm he, sigNat_zero, v2]
    exact sig0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h53c1, h53c2, h53c3, h53v⟩))))))))))
  have h54c1 : m + 2 ≤ (m + 4) := by omega
  have h54c2 : (m + 4) ≤ 2 * m - 4 := by omega
  have h54c3 : (m + 4) % 2 = 0 := by omega
  have h54v : 2 = ((m + 4) - m) / 2 := by
    omega
  have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t))))).val
      = 2 := by
    rw [sigF_val hm he, sigNat_zero, v3]
    exact sig0_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h54c1, h54c2, h54c3, h54v⟩)))))))))))
  have h5fc1 : (t + 3).val ≤ m / 2 - 2 := by omega
  have h5fv : 2 = (t + 3).val := by
    omega
  refine Fin.ext ?_
  rw [hiter, v4, iota_val hm]
  symm
  exact iota0_eq hm (Or.inl ⟨h5fc1, h5fv⟩)

set_option maxHeartbeats 1600000 in
private theorem chain1 {m : Nat} [NeZero m] [NeZero (m / 2)]
    (hm : 8 ≤ m) (he : m % 2 = 0) (t : ZMod (m / 2)) :
    (sigF 1 m)^[4] (iota 1 m t) = iota 1 m (t + 3) := by
  have hts := ZMod.val_lt t
  have ht3 := val_add3 hm t
  have hiter : (sigF 1 m)^[4] (iota 1 m t)
      = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))) :=
    rfl
  by_cases hc : t.val = 0
  · have h10c1 : t.val ≤ 1 := by omega
    have h10v : 0 = t.val := by
      omega
    have v0 : (iota 1 m t).val = 0 := by
      rw [iota_val hm]
      exact iota1_eq hm (Or.inl ⟨h10c1, h10v⟩)
    have h11c1 : 0 = 0 := by omega
    have h11v : m + 2 = m + 2 := by
      omega
    have v1 : (sigF 1 m (iota 1 m t)).val
        = m + 2 := by
      rw [sigF_val hm he, sigNat_one, v0]
      exact sig1_eq hm he (Or.inl ⟨h11c1, h11v⟩)
    have h12c1 : m ≤ (m + 2) := by omega
    have h12c2 : (m + 2) ≤ m + 3 := by omega
    have h12v : 2 = (m + 2) - m := by
      omega
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m t))).val
        = 2 := by
      rw [sigF_val hm he, sigNat_one, v1]
      exact sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h12c1, h12c2, h12v⟩))))))
    have h13c1 : 2 ≤ 2 := by omega
    have h13c2 : 2 ≤ m / 2 := by omega
    have h13v : m / 2 + 3 = 2 + m / 2 + 1 := by
      omega
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))).val
        = m / 2 + 3 := by
      rw [sigF_val hm he, sigNat_one, v2]
      exact sig1_eq hm he (Or.inr (Or.inr (Or.inl ⟨h13c1, h13c2, h13v⟩)))
    have h14c1 : m / 2 + 2 ≤ (m / 2 + 3) := by omega
    have h14c2 : (m / 2 + 3) ≤ m - 1 := by omega
    have h14v : m + 6 = 2 * (m / 2 + 3) := by
      omega
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))).val
        = m + 6 := by
      rw [sigF_val hm he, sigNat_one, v3]
      exact sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h14c1, h14c2, h14v⟩)))))
    have h1fc1 : 2 ≤ (t + 3).val := by omega
    have h1fv : m + 6 = m + 2 * (t + 3).val := by
      omega
    refine Fin.ext ?_
    rw [hiter, v4, iota_val hm]
    symm
    exact iota1_eq hm (Or.inr (⟨h1fc1, h1fv⟩))
  by_cases hc : t.val = 1
  · have h20c1 : t.val ≤ 1 := by omega
    have h20v : 1 = t.val := by
      omega
    have v0 : (iota 1 m t).val = 1 := by
      rw [iota_val hm]
      exact iota1_eq hm (Or.inl ⟨h20c1, h20v⟩)
    have h21c1 : 1 = 1 := by omega
    have h21v : m + 3 = m + 3 := by
      omega
    have v1 : (sigF 1 m (iota 1 m t)).val
        = m + 3 := by
      rw [sigF_val hm he, sigNat_one, v0]
      exact sig1_eq hm he (Or.inr (Or.inl ⟨h21c1, h21v⟩))
    have h22c1 : m ≤ (m + 3) := by omega
    have h22c2 : (m + 3) ≤ m + 3 := by omega
    have h22v : 3 = (m + 3) - m := by
      omega
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m t))).val
        = 3 := by
      rw [sigF_val hm he, sigNat_one, v1]
      exact sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h22c1, h22c2, h22v⟩))))))
    have h23c1 : 2 ≤ 3 := by omega
    have h23c2 : 3 ≤ m / 2 := by omega
    have h23v : m / 2 + 4 = 3 + m / 2 + 1 := by
      omega
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))).val
        = m / 2 + 4 := by
      rw [sigF_val hm he, sigNat_one, v2]
      exact sig1_eq hm he (Or.inr (Or.inr (Or.inl ⟨h23c1, h23c2, h23v⟩)))
    by_cases hh : m / 2 = 4
    · have h24ac1 : m ≤ (m / 2 + 4) := by omega
      have h24ac2 : (m / 2 + 4) ≤ m + 3 := by omega
      have h24av : 0 = (m / 2 + 4) - m := by
        omega
      have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))).val = 0 := by
        rw [sigF_val hm he, sigNat_one, v3]
        exact sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h24ac1, h24ac2, h24av⟩))))))
      have h2fac1 : (t + 3).val ≤ 1 := by omega
      have h2fav : 0 = (t + 3).val := by
        omega
      refine Fin.ext ?_
      rw [hiter, v4, iota_val hm]
      symm
      exact iota1_eq hm (Or.inl ⟨h2fac1, h2fav⟩)
    · have h24bc1 : m / 2 + 2 ≤ (m / 2 + 4) := by omega
      have h24bc2 : (m / 2 + 4) ≤ m - 1 := by omega
      have h24bv : m + 8 = 2 * (m / 2 + 4) := by
        omega
      have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))).val = m + 8 := by
        rw [sigF_val hm he, sigNat_one, v3]
        exact sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h24bc1, h24bc2, h24bv⟩)))))
      have h2fbc1 : 2 ≤ (t + 3).val := by omega
      have h2fbv : m + 8 = m + 2 * (t + 3).val := by
        omega
      refine Fin.ext ?_
      rw [hiter, v4, iota_val hm]
      symm
      exact iota1_eq hm (Or.inr (⟨h2fbc1, h2fbv⟩))
  by_cases hc : t.val ≤ m / 2 - 4
  · have h30c1 : 2 ≤ t.val := by omega
    have h30v : m + 2 * t.val = m + 2 * t.val := by
      omega
    have v0 : (iota 1 m t).val = m + 2 * t.val := by
      rw [iota_val hm]
      exact iota1_eq hm (Or.inr (⟨h30c1, h30v⟩))
    have h31c1 : m + 4 ≤ (m + 2 * t.val) := by omega
    have h31c2 : (m + 2 * t.val) ≤ 2 * m - 2 := by omega
    have h31c3 : (m + 2 * t.val) % 2 = 0 := by omega
    have h31v : m + 2 * t.val + 1 = (m + 2 * t.val) + 1 := by
      omega
    have v1 : (sigF 1 m (iota 1 m t)).val
        = m + 2 * t.val + 1 := by
      rw [sigF_val hm he, sigNat_one, v0]
      exact sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h31c1, h31c2, h31c3, h31v⟩))))))))
    have h32c1 : m + 5 ≤ (m + 2 * t.val + 1) := by omega
    have h32c2 : (m + 2 * t.val + 1) ≤ 2 * m - 3 := by omega
    have h32c3 : (m + 2 * t.val + 1) % 2 = 1 := by omega
    have h32v : t.val + 2 = ((m + 2 * t.val + 1) - m + 3) / 2 := by
      omega
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m t))).val
        = t.val + 2 := by
      rw [sigF_val hm he, sigNat_one, v1]
      exact sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h32c1, h32c2, h32c3, h32v⟩)))))))))
    have h33c1 : 2 ≤ (t.val + 2) := by omega
    have h33c2 : (t.val + 2) ≤ m / 2 := by omega
    have h33v : t.val + m / 2 + 3 = (t.val + 2) + m / 2 + 1 := by
      omega
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))).val
        = t.val + m / 2 + 3 := by
      rw [sigF_val hm he, sigNat_one, v2]
      exact sig1_eq hm he (Or.inr (Or.inr (Or.inl ⟨h33c1, h33c2, h33v⟩)))
    have h34c1 : m / 2 + 2 ≤ (t.val + m / 2 + 3) := by omega
    have h34c2 : (t.val + m / 2 + 3) ≤ m - 1 := by omega
    have h34v : 2 * t.val + m + 6 = 2 * (t.val + m / 2 + 3) := by
      omega
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))).val
        = 2 * t.val + m + 6 := by
      rw [sigF_val hm he, sigNat_one, v3]
      exact sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h34c1, h34c2, h34v⟩)))))
    have h3fc1 : 2 ≤ (t + 3).val := by omega
    have h3fv : 2 * t.val + m + 6 = m + 2 * (t + 3).val := by
      omega
    refine Fin.ext ?_
    rw [hiter, v4, iota_val hm]
    symm
    exact iota1_eq hm (Or.inr (⟨h3fc1, h3fv⟩))
  by_cases hc : t.val = m / 2 - 3
  · have h40c1 : 2 ≤ t.val := by omega
    have h40v : m + 2 * t.val = m + 2 * t.val := by
      omega
    have v0 : (iota 1 m t).val = m + 2 * t.val := by
      rw [iota_val hm]
      exact iota1_eq hm (Or.inr (⟨h40c1, h40v⟩))
    have h41c1 : m + 4 ≤ (m + 2 * t.val) := by omega
    have h41c2 : (m + 2 * t.val) ≤ 2 * m - 2 := by omega
    have h41c3 : (m + 2 * t.val) % 2 = 0 := by omega
    have h41v : 2 * m - 5 = (m + 2 * t.val) + 1 := by
      omega
    have v1 : (sigF 1 m (iota 1 m t)).val
        = 2 * m - 5 := by
      rw [sigF_val hm he, sigNat_one, v0]
      exact sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h41c1, h41c2, h41c3, h41v⟩))))))))
    have h42c1 : m + 5 ≤ (2 * m - 5) := by omega
    have h42c2 : (2 * m - 5) ≤ 2 * m - 3 := by omega
    have h42c3 : (2 * m - 5) % 2 = 1 := by omega
    have h42v : m / 2 - 1 = ((2 * m - 5) - m + 3) / 2 := by
      omega
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m t))).val
        = m / 2 - 1 := by
      rw [sigF_val hm he, sigNat_one, v1]
      exact sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h42c1, h42c2, h42c3, h42v⟩)))))))))
    have h43c1 : 2 ≤ (m / 2 - 1) := by omega
    have h43c2 : (m / 2 - 1) ≤ m / 2 := by omega
    have h43v : m = (m / 2 - 1) + m / 2 + 1 := by
      omega
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))).val
        = m := by
      rw [sigF_val hm he, sigNat_one, v2]
      exact sig1_eq hm he (Or.inr (Or.inr (Or.inl ⟨h43c1, h43c2, h43v⟩)))
    have h44c1 : m ≤ m := by omega
    have h44c2 : m ≤ m + 3 := by omega
    have h44v : 0 = m - m := by
      omega
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))).val
        = 0 := by
      rw [sigF_val hm he, sigNat_one, v3]
      exact sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h44c1, h44c2, h44v⟩))))))
    have h4fc1 : (t + 3).val ≤ 1 := by omega
    have h4fv : 0 = (t + 3).val := by
      omega
    refine Fin.ext ?_
    rw [hiter, v4, iota_val hm]
    symm
    exact iota1_eq hm (Or.inl ⟨h4fc1, h4fv⟩)
  by_cases hc : t.val = m / 2 - 2
  · have h50c1 : 2 ≤ t.val := by omega
    have h50v : m + 2 * t.val = m + 2 * t.val := by
      omega
    have v0 : (iota 1 m t).val = m + 2 * t.val := by
      rw [iota_val hm]
      exact iota1_eq hm (Or.inr (⟨h50c1, h50v⟩))
    have h51c1 : m + 4 ≤ (m + 2 * t.val) := by omega
    have h51c2 : (m + 2 * t.val) ≤ 2 * m - 2 := by omega
    have h51c3 : (m + 2 * t.val) % 2 = 0 := by omega
    have h51v : 2 * m - 3 = (m + 2 * t.val) + 1 := by
      omega
    have v1 : (sigF 1 m (iota 1 m t)).val
        = 2 * m - 3 := by
      rw [sigF_val hm he, sigNat_one, v0]
      exact sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h51c1, h51c2, h51c3, h51v⟩))))))))
    have h52c1 : m + 5 ≤ (2 * m - 3) := by omega
    have h52c2 : (2 * m - 3) ≤ 2 * m - 3 := by omega
    have h52c3 : (2 * m - 3) % 2 = 1 := by omega
    have h52v : m / 2 = ((2 * m - 3) - m + 3) / 2 := by
      omega
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m t))).val
        = m / 2 := by
      rw [sigF_val hm he, sigNat_one, v1]
      exact sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h52c1, h52c2, h52c3, h52v⟩)))))))))
    have h53c1 : 2 ≤ (m / 2) := by omega
    have h53c2 : (m / 2) ≤ m / 2 := by omega
    have h53v : m + 1 = (m / 2) + m / 2 + 1 := by
      omega
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))).val
        = m + 1 := by
      rw [sigF_val hm he, sigNat_one, v2]
      exact sig1_eq hm he (Or.inr (Or.inr (Or.inl ⟨h53c1, h53c2, h53v⟩)))
    have h54c1 : m ≤ (m + 1) := by omega
    have h54c2 : (m + 1) ≤ m + 3 := by omega
    have h54v : 1 = (m + 1) - m := by
      omega
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))).val
        = 1 := by
      rw [sigF_val hm he, sigNat_one, v3]
      exact sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h54c1, h54c2, h54v⟩))))))
    have h5fc1 : (t + 3).val ≤ 1 := by omega
    have h5fv : 1 = (t + 3).val := by
      omega
    refine Fin.ext ?_
    rw [hiter, v4, iota_val hm]
    symm
    exact iota1_eq hm (Or.inl ⟨h5fc1, h5fv⟩)
  have h60c1 : 2 ≤ t.val := by omega
  have h60v : 2 * m - 2 = m + 2 * t.val := by
    omega
  have v0 : (iota 1 m t).val = 2 * m - 2 := by
    rw [iota_val hm]
    exact iota1_eq hm (Or.inr (⟨h60c1, h60v⟩))
  have h61c1 : m + 4 ≤ (2 * m - 2) := by omega
  have h61c2 : (2 * m - 2) ≤ 2 * m - 2 := by omega
  have h61c3 : (2 * m - 2) % 2 = 0 := by omega
  have h61v : 2 * m - 1 = (2 * m - 2) + 1 := by
    omega
  have v1 : (sigF 1 m (iota 1 m t)).val
      = 2 * m - 1 := by
    rw [sigF_val hm he, sigNat_one, v0]
    exact sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h61c1, h61c2, h61c3, h61v⟩))))))))
  have h62c1 : (2 * m - 1) = 2 * m - 1 := by omega
  have h62v : m / 2 + 1 = m / 2 + 1 := by
    omega
  have v2 : (sigF 1 m (sigF 1 m (iota 1 m t))).val
      = m / 2 + 1 := by
    rw [sigF_val hm he, sigNat_one, v1]
    exact sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h62c1, h62v⟩)))))))
  have h63c1 : (m / 2 + 1) = m / 2 + 1 := by omega
  have h63v : m / 2 + 2 = m / 2 + 2 := by
    omega
  have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))).val
      = m / 2 + 2 := by
    rw [sigF_val hm he, sigNat_one, v2]
    exact sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inl ⟨h63c1, h63v⟩))))
  have h64c1 : m / 2 + 2 ≤ (m / 2 + 2) := by omega
  have h64c2 : (m / 2 + 2) ≤ m - 1 := by omega
  have h64v : m + 4 = 2 * (m / 2 + 2) := by
    omega
  have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))).val
      = m + 4 := by
    rw [sigF_val hm he, sigNat_one, v3]
    exact sig1_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h64c1, h64c2, h64v⟩)))))
  have h6fc1 : 2 ≤ (t + 3).val := by omega
  have h6fv : m + 4 = m + 2 * (t + 3).val := by
    omega
  refine Fin.ext ?_
  rw [hiter, v4, iota_val hm]
  symm
  exact iota1_eq hm (Or.inr (⟨h6fc1, h6fv⟩))

set_option maxHeartbeats 1600000 in
private theorem chain2 {m : Nat} [NeZero m] [NeZero (m / 2)]
    (hm : 8 ≤ m) (he : m % 2 = 0) (t : ZMod (m / 2)) :
    (sigF 2 m)^[4] (iota 2 m t) = iota 2 m (t + 3) := by
  have hts := ZMod.val_lt t
  have ht3 := val_add3 hm t
  have hiter : (sigF 2 m)^[4] (iota 2 m t)
      = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))) :=
    rfl
  by_cases hc : t.val = 0
  · have h10c1 : t.val ≤ m / 2 - 2 := by omega
    have h10v : 0 = 2 * t.val := by
      omega
    have v0 : (iota 2 m t).val = 0 := by
      rw [iota_val hm]
      exact iota2_eq hm (Or.inl ⟨h10c1, h10v⟩)
    have h11c1 : 0 = 0 := by omega
    have h11v : m = m := by
      omega
    have v1 : (sigF 2 m (iota 2 m t)).val
        = m := by
      rw [sigF_val hm he, sigNat_two, v0]
      exact sig2_eq hm he (Or.inl ⟨h11c1, h11v⟩)
    have h12c1 : m ≤ m := by omega
    have h12c2 : m ≤ m + m / 2 - 3 := by omega
    have h12v : m + m / 2 + 1 = m + m / 2 + 1 := by
      omega
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m t))).val
        = m + m / 2 + 1 := by
      rw [sigF_val hm he, sigNat_two, v1]
      exact sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h12c1, h12c2, h12v⟩)))))))
    have h13c1 : m + m / 2 - 1 ≤ (m + m / 2 + 1) := by omega
    have h13c2 : (m + m / 2 + 1) ≤ 2 * m - 3 := by omega
    have h13v : 5 = 2 * (m + m / 2 + 1) + 3 - 3 * m := by
      omega
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))).val
        = 5 := by
      rw [sigF_val hm he, sigNat_two, v2]
      exact sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h13c1, h13c2, h13v⟩)))))))))
    by_cases hh : m / 2 = 4
    · have h14ac1 : 5 = m - 3 := by omega
      have h14av : 2 * m - 1 = 2 * m - 1 := by
        omega
      have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))).val = 2 * m - 1 := by
        rw [sigF_val hm he, sigNat_two, v3]
        exact sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inl ⟨h14ac1, h14av⟩))))
      have h1fac1 : m / 2 - 2 < (t + 3).val := by omega
      have h1fav : 2 * m - 1 = 2 * m - 1 := by
        omega
      refine Fin.ext ?_
      rw [hiter, v4, iota_val hm]
      symm
      exact iota2_eq hm (Or.inr (⟨h1fac1, h1fav⟩))
    · have h14bc1 : 1 ≤ 5 := by omega
      have h14bc2 : 5 ≤ m - 4 := by omega
      have h14bc3 : 5 % 2 = 1 := by omega
      have h14bv : 6 = 5 + 1 := by
        omega
      have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))).val = 6 := by
        rw [sigF_val hm he, sigNat_two, v3]
        exact sig2_eq hm he (Or.inr (Or.inl ⟨h14bc1, h14bc2, h14bc3, h14bv⟩))
      have h1fbc1 : (t + 3).val ≤ m / 2 - 2 := by omega
      have h1fbv : 6 = 2 * (t + 3).val := by
        omega
      refine Fin.ext ?_
      rw [hiter, v4, iota_val hm]
      symm
      exact iota2_eq hm (Or.inl ⟨h1fbc1, h1fbv⟩)
  by_cases hc : t.val + 5 ≤ m / 2
  · have h20c1 : t.val ≤ m / 2 - 2 := by omega
    have h20v : 2 * t.val = 2 * t.val := by
      omega
    have v0 : (iota 2 m t).val = 2 * t.val := by
      rw [iota_val hm]
      exact iota2_eq hm (Or.inl ⟨h20c1, h20v⟩)
    have h21c1 : 2 ≤ (2 * t.val) := by omega
    have h21c2 : (2 * t.val) ≤ m - 4 := by omega
    have h21c3 : (2 * t.val) % 2 = 0 := by omega
    have h21v : t.val + m = (2 * t.val) / 2 + m := by
      omega
    have v1 : (sigF 2 m (iota 2 m t)).val
        = t.val + m := by
      rw [sigF_val hm he, sigNat_two, v0]
      exact sig2_eq hm he (Or.inr (Or.inr (Or.inl ⟨h21c1, h21c2, h21c3, h21v⟩)))
    have h22c1 : m ≤ (t.val + m) := by omega
    have h22c2 : (t.val + m) ≤ m + m / 2 - 3 := by omega
    have h22v : t.val + m + m / 2 + 1 = (t.val + m) + m / 2 + 1 := by
      omega
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m t))).val
        = t.val + m + m / 2 + 1 := by
      rw [sigF_val hm he, sigNat_two, v1]
      exact sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h22c1, h22c2, h22v⟩)))))))
    have h23c1 : m + m / 2 - 1 ≤ (t.val + m + m / 2 + 1) := by omega
    have h23c2 : (t.val + m + m / 2 + 1) ≤ 2 * m - 3 := by omega
    have h23v : 2 * t.val + 5 = 2 * (t.val + m + m / 2 + 1) + 3 - 3 * m := by
      omega
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))).val
        = 2 * t.val + 5 := by
      rw [sigF_val hm he, sigNat_two, v2]
      exact sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h23c1, h23c2, h23v⟩)))))))))
    have h24c1 : 1 ≤ (2 * t.val + 5) := by omega
    have h24c2 : (2 * t.val + 5) ≤ m - 4 := by omega
    have h24c3 : (2 * t.val + 5) % 2 = 1 := by omega
    have h24v : 2 * t.val + 6 = (2 * t.val + 5) + 1 := by
      omega
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))).val
        = 2 * t.val + 6 := by
      rw [sigF_val hm he, sigNat_two, v3]
      exact sig2_eq hm he (Or.inr (Or.inl ⟨h24c1, h24c2, h24c3, h24v⟩))
    have h2fc1 : (t + 3).val ≤ m / 2 - 2 := by omega
    have h2fv : 2 * t.val + 6 = 2 * (t + 3).val := by
      omega
    refine Fin.ext ?_
    rw [hiter, v4, iota_val hm]
    symm
    exact iota2_eq hm (Or.inl ⟨h2fc1, h2fv⟩)
  by_cases hc : t.val = m / 2 - 4
  · have h30c1 : t.val ≤ m / 2 - 2 := by omega
    have h30v : 2 * t.val = 2 * t.val := by
      omega
    have v0 : (iota 2 m t).val = 2 * t.val := by
      rw [iota_val hm]
      exact iota2_eq hm (Or.inl ⟨h30c1, h30v⟩)
    have h31c1 : 2 ≤ (2 * t.val) := by omega
    have h31c2 : (2 * t.val) ≤ m - 4 := by omega
    have h31c3 : (2 * t.val) % 2 = 0 := by omega
    have h31v : m + m / 2 - 4 = (2 * t.val) / 2 + m := by
      omega
    have v1 : (sigF 2 m (iota 2 m t)).val
        = m + m / 2 - 4 := by
      rw [sigF_val hm he, sigNat_two, v0]
      exact sig2_eq hm he (Or.inr (Or.inr (Or.inl ⟨h31c1, h31c2, h31c3, h31v⟩)))
    have h32c1 : m ≤ (m + m / 2 - 4) := by omega
    have h32c2 : (m + m / 2 - 4) ≤ m + m / 2 - 3 := by omega
    have h32v : 2 * m - 3 = (m + m / 2 - 4) + m / 2 + 1 := by
      omega
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m t))).val
        = 2 * m - 3 := by
      rw [sigF_val hm he, sigNat_two, v1]
      exact sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h32c1, h32c2, h32v⟩)))))))
    have h33c1 : m + m / 2 - 1 ≤ (2 * m - 3) := by omega
    have h33c2 : (2 * m - 3) ≤ 2 * m - 3 := by omega
    have h33v : m - 3 = 2 * (2 * m - 3) + 3 - 3 * m := by
      omega
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))).val
        = m - 3 := by
      rw [sigF_val hm he, sigNat_two, v2]
      exact sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h33c1, h33c2, h33v⟩)))))))))
    have h34c1 : (m - 3) = m - 3 := by omega
    have h34v : 2 * m - 1 = 2 * m - 1 := by
      omega
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))).val
        = 2 * m - 1 := by
      rw [sigF_val hm he, sigNat_two, v3]
      exact sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inl ⟨h34c1, h34v⟩))))
    have h3fc1 : m / 2 - 2 < (t + 3).val := by omega
    have h3fv : 2 * m - 1 = 2 * m - 1 := by
      omega
    refine Fin.ext ?_
    rw [hiter, v4, iota_val hm]
    symm
    exact iota2_eq hm (Or.inr (⟨h3fc1, h3fv⟩))
  by_cases hc : t.val = m / 2 - 3
  · have h40c1 : t.val ≤ m / 2 - 2 := by omega
    have h40v : 2 * t.val = 2 * t.val := by
      omega
    have v0 : (iota 2 m t).val = 2 * t.val := by
      rw [iota_val hm]
      exact iota2_eq hm (Or.inl ⟨h40c1, h40v⟩)
    have h41c1 : 2 ≤ (2 * t.val) := by omega
    have h41c2 : (2 * t.val) ≤ m - 4 := by omega
    have h41c3 : (2 * t.val) % 2 = 0 := by omega
    have h41v : m + m / 2 - 3 = (2 * t.val) / 2 + m := by
      omega
    have v1 : (sigF 2 m (iota 2 m t)).val
        = m + m / 2 - 3 := by
      rw [sigF_val hm he, sigNat_two, v0]
      exact sig2_eq hm he (Or.inr (Or.inr (Or.inl ⟨h41c1, h41c2, h41c3, h41v⟩)))
    have h42c1 : m ≤ (m + m / 2 - 3) := by omega
    have h42c2 : (m + m / 2 - 3) ≤ m + m / 2 - 3 := by omega
    have h42v : 2 * m - 2 = (m + m / 2 - 3) + m / 2 + 1 := by
      omega
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m t))).val
        = 2 * m - 2 := by
      rw [sigF_val hm he, sigNat_two, v1]
      exact sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h42c1, h42c2, h42v⟩)))))))
    have h43c1 : (2 * m - 2) = 2 * m - 2 := by omega
    have h43v : m - 2 = m - 2 := by
      omega
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))).val
        = m - 2 := by
      rw [sigF_val hm he, sigNat_two, v2]
      exact sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h43c1, h43v⟩))))))))))
    have h44c1 : (m - 2) = m - 2 := by omega
    have h44v : 0 = 0 := by
      omega
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))).val
        = 0 := by
      rw [sigF_val hm he, sigNat_two, v3]
      exact sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h44c1, h44v⟩)))))
    have h4fc1 : (t + 3).val ≤ m / 2 - 2 := by omega
    have h4fv : 0 = 2 * (t + 3).val := by
      omega
    refine Fin.ext ?_
    rw [hiter, v4, iota_val hm]
    symm
    exact iota2_eq hm (Or.inl ⟨h4fc1, h4fv⟩)
  by_cases hc : t.val = m / 2 - 2
  · have h50c1 : t.val ≤ m / 2 - 2 := by omega
    have h50v : m - 4 = 2 * t.val := by
      omega
    have v0 : (iota 2 m t).val = m - 4 := by
      rw [iota_val hm]
      exact iota2_eq hm (Or.inl ⟨h50c1, h50v⟩)
    have h51c1 : 2 ≤ (m - 4) := by omega
    have h51c2 : (m - 4) ≤ m - 4 := by omega
    have h51c3 : (m - 4) % 2 = 0 := by omega
    have h51v : m + m / 2 - 2 = (m - 4) / 2 + m := by
      omega
    have v1 : (sigF 2 m (iota 2 m t)).val
        = m + m / 2 - 2 := by
      rw [sigF_val hm he, sigNat_two, v0]
      exact sig2_eq hm he (Or.inr (Or.inr (Or.inl ⟨h51c1, h51c2, h51c3, h51v⟩)))
    have h52c1 : (m + m / 2 - 2) = m + m / 2 - 2 := by omega
    have h52v : m + m / 2 - 1 = (m + m / 2 - 2) + 1 := by
      omega
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m t))).val
        = m + m / 2 - 1 := by
      rw [sigF_val hm he, sigNat_two, v1]
      exact sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h52c1, h52v⟩))))))))
    have h53c1 : m + m / 2 - 1 ≤ (m + m / 2 - 1) := by omega
    have h53c2 : (m + m / 2 - 1) ≤ 2 * m - 3 := by omega
    have h53v : 1 = 2 * (m + m / 2 - 1) + 3 - 3 * m := by
      omega
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))).val
        = 1 := by
      rw [sigF_val hm he, sigNat_two, v2]
      exact sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h53c1, h53c2, h53v⟩)))))))))
    have h54c1 : 1 ≤ 1 := by omega
    have h54c2 : 1 ≤ m - 4 := by omega
    have h54c3 : 1 % 2 = 1 := by omega
    have h54v : 2 = 1 + 1 := by
      omega
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))).val
        = 2 := by
      rw [sigF_val hm he, sigNat_two, v3]
      exact sig2_eq hm he (Or.inr (Or.inl ⟨h54c1, h54c2, h54c3, h54v⟩))
    have h5fc1 : (t + 3).val ≤ m / 2 - 2 := by omega
    have h5fv : 2 = 2 * (t + 3).val := by
      omega
    refine Fin.ext ?_
    rw [hiter, v4, iota_val hm]
    symm
    exact iota2_eq hm (Or.inl ⟨h5fc1, h5fv⟩)
  have h60c1 : m / 2 - 2 < t.val := by omega
  have h60v : 2 * m - 1 = 2 * m - 1 := by
    omega
  have v0 : (iota 2 m t).val = 2 * m - 1 := by
    rw [iota_val hm]
    exact iota2_eq hm (Or.inr (⟨h60c1, h60v⟩))
  have h61c1 : (2 * m - 1) = 2 * m - 1 := by omega
  have h61v : m - 1 = m - 1 := by
    omega
  have v1 : (sigF 2 m (iota 2 m t)).val
      = m - 1 := by
    rw [sigF_val hm he, sigNat_two, v0]
    exact sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h61c1, h61v⟩)))))))))))
  have h62c1 : (m - 1) = m - 1 := by omega
  have h62v : m + m / 2 = m + m / 2 := by
    omega
  have v2 : (sigF 2 m (sigF 2 m (iota 2 m t))).val
      = m + m / 2 := by
    rw [sigF_val hm he, sigNat_two, v1]
    exact sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h62c1, h62v⟩))))))
  have h63c1 : m + m / 2 - 1 ≤ (m + m / 2) := by omega
  have h63c2 : (m + m / 2) ≤ 2 * m - 3 := by omega
  have h63v : 3 = 2 * (m + m / 2) + 3 - 3 * m := by
    omega
  have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))).val
      = 3 := by
    rw [sigF_val hm he, sigNat_two, v2]
    exact sig2_eq hm he (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h63c1, h63c2, h63v⟩)))))))))
  have h64c1 : 1 ≤ 3 := by omega
  have h64c2 : 3 ≤ m - 4 := by omega
  have h64c3 : 3 % 2 = 1 := by omega
  have h64v : 4 = 3 + 1 := by
    omega
  have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))).val
      = 4 := by
    rw [sigF_val hm he, sigNat_two, v3]
    exact sig2_eq hm he (Or.inr (Or.inl ⟨h64c1, h64c2, h64c3, h64v⟩))
  have h6fc1 : (t + 3).val ≤ m / 2 - 2 := by omega
  have h6fv : 4 = 2 * (t + 3).val := by
    omega
  refine Fin.ext ?_
  rw [hiter, v4, iota_val hm]
  symm
  exact iota2_eq hm (Or.inl ⟨h6fc1, h6fv⟩)

set_option maxHeartbeats 1600000 in
private theorem cover0 {m : Nat} [NeZero m] [NeZero (m / 2)]
    (hm : 8 ≤ m) (he : m % 2 = 0) (k : Fin (2 * m)) :
    ∃ t : ZMod (m / 2), ∃ j : Nat, j < 4 ∧ (sigF 0 m)^[j] (iota 0 m t) = k := by
  have hk := k.isLt
  by_cases hcc : k.val ≤ m / 2 - 2
  · refine ⟨((k.val : Nat) : ZMod (m / 2)), 0, by omega, ?_⟩
    have hts : (((k.val : Nat) : ZMod (m / 2))).val = k.val :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 0 m (((k.val : Nat) : ZMod (m / 2)))).val = k.val := by
      rw [iota_val hm, hts]
      apply iota0_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have hit : (sigF 0 m)^[0] (iota 0 m (((k.val : Nat) : ZMod (m / 2))))
        = iota 0 m (((k.val : Nat) : ZMod (m / 2))) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hcc : k.val = 2 * m - 1
  · refine ⟨((m / 2 - 1 : Nat) : ZMod (m / 2)), 0, by omega, ?_⟩
    have hts : (((m / 2 - 1 : Nat) : ZMod (m / 2))).val = m / 2 - 1 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 0 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))).val = 2 * m - 1 := by
      rw [iota_val hm, hts]
      apply iota0_eq hm
      exact Or.inr (⟨by omega, by omega⟩)
    have hit : (sigF 0 m)^[0] (iota 0 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))
        = iota 0 m (((m / 2 - 1 : Nat) : ZMod (m / 2))) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hcc : k.val = m / 2 - 1
  · refine ⟨((m / 2 - 2 : Nat) : ZMod (m / 2)), 1, by omega, ?_⟩
    have hts : (((m / 2 - 2 : Nat) : ZMod (m / 2))).val = m / 2 - 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 0 m (((m / 2 - 2 : Nat) : ZMod (m / 2)))).val = m / 2 - 2 := by
      rw [iota_val hm, hts]
      apply iota0_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 0 m (iota 0 m (((m / 2 - 2 : Nat) : ZMod (m / 2))))).val
        = m / 2 - 1 := by
      rw [sigF_val hm he, sigNat_zero, v0]
      apply sig0_eq hm he
      exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    have hit : (sigF 0 m)^[1] (iota 0 m (((m / 2 - 2 : Nat) : ZMod (m / 2))))
        = sigF 0 m (iota 0 m (((m / 2 - 2 : Nat) : ZMod (m / 2)))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hcc : k.val = m / 2
  · refine ⟨((m / 2 - 1 : Nat) : ZMod (m / 2)), 1, by omega, ?_⟩
    have hts : (((m / 2 - 1 : Nat) : ZMod (m / 2))).val = m / 2 - 1 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 0 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))).val = 2 * m - 1 := by
      rw [iota_val hm, hts]
      apply iota0_eq hm
      exact Or.inr (⟨by omega, by omega⟩)
    have v1 : (sigF 0 m (iota 0 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))).val
        = m / 2 := by
      rw [sigF_val hm he, sigNat_zero, v0]
      apply sig0_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))))
    have hit : (sigF 0 m)^[1] (iota 0 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))
        = sigF 0 m (iota 0 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hcc : k.val ≤ m - 2
  · refine ⟨((k.val - m / 2 - 1 : Nat) : ZMod (m / 2)), 1, by omega, ?_⟩
    have hts : (((k.val - m / 2 - 1 : Nat) : ZMod (m / 2))).val = k.val - m / 2 - 1 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 0 m (((k.val - m / 2 - 1 : Nat) : ZMod (m / 2)))).val = k.val - m / 2 - 1 := by
      rw [iota_val hm, hts]
      apply iota0_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 0 m (iota 0 m (((k.val - m / 2 - 1 : Nat) : ZMod (m / 2))))).val
        = k.val := by
      rw [sigF_val hm he, sigNat_zero, v0]
      apply sig0_eq hm he
      exact Or.inl ⟨by omega, by omega⟩
    have hit : (sigF 0 m)^[1] (iota 0 m (((k.val - m / 2 - 1 : Nat) : ZMod (m / 2))))
        = sigF 0 m (iota 0 m (((k.val - m / 2 - 1 : Nat) : ZMod (m / 2)))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hcc : k.val = m - 1
  · refine ⟨((m / 2 - 4 : Nat) : ZMod (m / 2)), 3, by omega, ?_⟩
    have hts : (((m / 2 - 4 : Nat) : ZMod (m / 2))).val = m / 2 - 4 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 0 m (((m / 2 - 4 : Nat) : ZMod (m / 2)))).val = m / 2 - 4 := by
      rw [iota_val hm, hts]
      apply iota0_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 0 m (iota 0 m (((m / 2 - 4 : Nat) : ZMod (m / 2))))).val
        = m - 3 := by
      rw [sigF_val hm he, sigNat_zero, v0]
      apply sig0_eq hm he
      exact Or.inl ⟨by omega, by omega⟩
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 2 - 4 : Nat) : ZMod (m / 2)))))).val
        = 2 * m - 3 := by
      rw [sigF_val hm he, sigNat_zero, v1]
      apply sig0_eq hm he
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 2 - 4 : Nat) : ZMod (m / 2))))))).val
        = m - 1 := by
      rw [sigF_val hm he, sigNat_zero, v2]
      apply sig0_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))
    have hit : (sigF 0 m)^[3] (iota 0 m (((m / 2 - 4 : Nat) : ZMod (m / 2))))
        = sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 2 - 4 : Nat) : ZMod (m / 2)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hcc : k.val = m
  · refine ⟨((m / 2 - 3 : Nat) : ZMod (m / 2)), 3, by omega, ?_⟩
    have hts : (((m / 2 - 3 : Nat) : ZMod (m / 2))).val = m / 2 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 0 m (((m / 2 - 3 : Nat) : ZMod (m / 2)))).val = m / 2 - 3 := by
      rw [iota_val hm, hts]
      apply iota0_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 0 m (iota 0 m (((m / 2 - 3 : Nat) : ZMod (m / 2))))).val
        = m - 2 := by
      rw [sigF_val hm he, sigNat_zero, v0]
      apply sig0_eq hm he
      exact Or.inl ⟨by omega, by omega⟩
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 2 - 3 : Nat) : ZMod (m / 2)))))).val
        = 2 * m - 2 := by
      rw [sigF_val hm he, sigNat_zero, v1]
      apply sig0_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 2 - 3 : Nat) : ZMod (m / 2))))))).val
        = m := by
      rw [sigF_val hm he, sigNat_zero, v2]
      apply sig0_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))))
    have hit : (sigF 0 m)^[3] (iota 0 m (((m / 2 - 3 : Nat) : ZMod (m / 2))))
        = sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 2 - 3 : Nat) : ZMod (m / 2)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hcc : k.val = m + 1
  · refine ⟨((m / 2 - 2 : Nat) : ZMod (m / 2)), 2, by omega, ?_⟩
    have hts : (((m / 2 - 2 : Nat) : ZMod (m / 2))).val = m / 2 - 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 0 m (((m / 2 - 2 : Nat) : ZMod (m / 2)))).val = m / 2 - 2 := by
      rw [iota_val hm, hts]
      apply iota0_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 0 m (iota 0 m (((m / 2 - 2 : Nat) : ZMod (m / 2))))).val
        = m / 2 - 1 := by
      rw [sigF_val hm he, sigNat_zero, v0]
      apply sig0_eq hm he
      exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 2 - 2 : Nat) : ZMod (m / 2)))))).val
        = m + 1 := by
      rw [sigF_val hm he, sigNat_zero, v1]
      apply sig0_eq hm he
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
    have hit : (sigF 0 m)^[2] (iota 0 m (((m / 2 - 2 : Nat) : ZMod (m / 2))))
        = sigF 0 m (sigF 0 m (iota 0 m (((m / 2 - 2 : Nat) : ZMod (m / 2))))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hcc : k.val = m + 2
  · refine ⟨((m / 2 - 2 : Nat) : ZMod (m / 2)), 3, by omega, ?_⟩
    have hts : (((m / 2 - 2 : Nat) : ZMod (m / 2))).val = m / 2 - 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 0 m (((m / 2 - 2 : Nat) : ZMod (m / 2)))).val = m / 2 - 2 := by
      rw [iota_val hm, hts]
      apply iota0_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 0 m (iota 0 m (((m / 2 - 2 : Nat) : ZMod (m / 2))))).val
        = m / 2 - 1 := by
      rw [sigF_val hm he, sigNat_zero, v0]
      apply sig0_eq hm he
      exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 2 - 2 : Nat) : ZMod (m / 2)))))).val
        = m + 1 := by
      rw [sigF_val hm he, sigNat_zero, v1]
      apply sig0_eq hm he
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 2 - 2 : Nat) : ZMod (m / 2))))))).val
        = m + 2 := by
      rw [sigF_val hm he, sigNat_zero, v2]
      apply sig0_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)))))))))
    have hit : (sigF 0 m)^[3] (iota 0 m (((m / 2 - 2 : Nat) : ZMod (m / 2))))
        = sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 2 - 2 : Nat) : ZMod (m / 2)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hcc : k.val = m + 3
  · refine ⟨((m / 2 - 1 : Nat) : ZMod (m / 2)), 2, by omega, ?_⟩
    have hts : (((m / 2 - 1 : Nat) : ZMod (m / 2))).val = m / 2 - 1 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 0 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))).val = 2 * m - 1 := by
      rw [iota_val hm, hts]
      apply iota0_eq hm
      exact Or.inr (⟨by omega, by omega⟩)
    have v1 : (sigF 0 m (iota 0 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))).val
        = m / 2 := by
      rw [sigF_val hm he, sigNat_zero, v0]
      apply sig0_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))))).val
        = m + 3 := by
      rw [sigF_val hm he, sigNat_zero, v1]
      apply sig0_eq hm he
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
    have hit : (sigF 0 m)^[2] (iota 0 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))
        = sigF 0 m (sigF 0 m (iota 0 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hcc : k.val = m + 4
  · refine ⟨((m / 2 - 1 : Nat) : ZMod (m / 2)), 3, by omega, ?_⟩
    have hts : (((m / 2 - 1 : Nat) : ZMod (m / 2))).val = m / 2 - 1 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 0 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))).val = 2 * m - 1 := by
      rw [iota_val hm, hts]
      apply iota0_eq hm
      exact Or.inr (⟨by omega, by omega⟩)
    have v1 : (sigF 0 m (iota 0 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))).val
        = m / 2 := by
      rw [sigF_val hm he, sigNat_zero, v0]
      apply sig0_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))))).val
        = m + 3 := by
      rw [sigF_val hm he, sigNat_zero, v1]
      apply sig0_eq hm he
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))))).val
        = m + 4 := by
      rw [sigF_val hm he, sigNat_zero, v2]
      apply sig0_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)))))))))
    have hit : (sigF 0 m)^[3] (iota 0 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))
        = sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hcc : k.val = 2 * m - 2
  · refine ⟨((m / 2 - 3 : Nat) : ZMod (m / 2)), 2, by omega, ?_⟩
    have hts : (((m / 2 - 3 : Nat) : ZMod (m / 2))).val = m / 2 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 0 m (((m / 2 - 3 : Nat) : ZMod (m / 2)))).val = m / 2 - 3 := by
      rw [iota_val hm, hts]
      apply iota0_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 0 m (iota 0 m (((m / 2 - 3 : Nat) : ZMod (m / 2))))).val
        = m - 2 := by
      rw [sigF_val hm he, sigNat_zero, v0]
      apply sig0_eq hm he
      exact Or.inl ⟨by omega, by omega⟩
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 2 - 3 : Nat) : ZMod (m / 2)))))).val
        = 2 * m - 2 := by
      rw [sigF_val hm he, sigNat_zero, v1]
      apply sig0_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    have hit : (sigF 0 m)^[2] (iota 0 m (((m / 2 - 3 : Nat) : ZMod (m / 2))))
        = sigF 0 m (sigF 0 m (iota 0 m (((m / 2 - 3 : Nat) : ZMod (m / 2))))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hcc : k.val % 2 = 1
  · refine ⟨(((k.val - m - 5) / 2 : Nat) : ZMod (m / 2)), 2, by omega, ?_⟩
    have hts : ((((k.val - m - 5) / 2 : Nat) : ZMod (m / 2))).val = (k.val - m - 5) / 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 0 m ((((k.val - m - 5) / 2 : Nat) : ZMod (m / 2)))).val = (k.val - m - 5) / 2 := by
      rw [iota_val hm, hts]
      apply iota0_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 0 m (iota 0 m ((((k.val - m - 5) / 2 : Nat) : ZMod (m / 2))))).val
        = (k.val - m - 5) / 2 + m / 2 + 1 := by
      rw [sigF_val hm he, sigNat_zero, v0]
      apply sig0_eq hm he
      exact Or.inl ⟨by omega, by omega⟩
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m ((((k.val - m - 5) / 2 : Nat) : ZMod (m / 2)))))).val
        = k.val := by
      rw [sigF_val hm he, sigNat_zero, v1]
      apply sig0_eq hm he
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
    have hit : (sigF 0 m)^[2] (iota 0 m ((((k.val - m - 5) / 2 : Nat) : ZMod (m / 2))))
        = sigF 0 m (sigF 0 m (iota 0 m ((((k.val - m - 5) / 2 : Nat) : ZMod (m / 2))))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  refine ⟨(((k.val - m - 6) / 2 : Nat) : ZMod (m / 2)), 3, by omega, ?_⟩
  have hts : ((((k.val - m - 6) / 2 : Nat) : ZMod (m / 2))).val = (k.val - m - 6) / 2 :=
    ZMod.val_natCast_of_lt (by omega)
  have v0 : (iota 0 m ((((k.val - m - 6) / 2 : Nat) : ZMod (m / 2)))).val = (k.val - m - 6) / 2 := by
    rw [iota_val hm, hts]
    apply iota0_eq hm
    exact Or.inl ⟨by omega, by omega⟩
  have v1 : (sigF 0 m (iota 0 m ((((k.val - m - 6) / 2 : Nat) : ZMod (m / 2))))).val
      = (k.val - m - 6) / 2 + m / 2 + 1 := by
    rw [sigF_val hm he, sigNat_zero, v0]
    apply sig0_eq hm he
    exact Or.inl ⟨by omega, by omega⟩
  have v2 : (sigF 0 m (sigF 0 m (iota 0 m ((((k.val - m - 6) / 2 : Nat) : ZMod (m / 2)))))).val
      = 2 * ((k.val - m - 6) / 2) + m + 5 := by
    rw [sigF_val hm he, sigNat_zero, v1]
    apply sig0_eq hm he
    exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
  have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m ((((k.val - m - 6) / 2 : Nat) : ZMod (m / 2))))))).val
      = k.val := by
    rw [sigF_val hm he, sigNat_zero, v2]
    apply sig0_eq hm he
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)))))))))
  have hit : (sigF 0 m)^[3] (iota 0 m ((((k.val - m - 6) / 2 : Nat) : ZMod (m / 2))))
      = sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m ((((k.val - m - 6) / 2 : Nat) : ZMod (m / 2)))))) := rfl
  refine Fin.ext ?_
  rw [hit, v3]
  all_goals omega

set_option maxHeartbeats 1600000 in
private theorem cover1 {m : Nat} [NeZero m] [NeZero (m / 2)]
    (hm : 8 ≤ m) (he : m % 2 = 0) (k : Fin (2 * m)) :
    ∃ t : ZMod (m / 2), ∃ j : Nat, j < 4 ∧ (sigF 1 m)^[j] (iota 1 m t) = k := by
  have hk := k.isLt
  by_cases hcc : k.val = 0
  · refine ⟨((0 : Nat) : ZMod (m / 2)), 0, by omega, ?_⟩
    have hts : (((0 : Nat) : ZMod (m / 2))).val = 0 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 1 m (((0 : Nat) : ZMod (m / 2)))).val = 0 := by
      rw [iota_val hm, hts]
      apply iota1_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have hit : (sigF 1 m)^[0] (iota 1 m (((0 : Nat) : ZMod (m / 2))))
        = iota 1 m (((0 : Nat) : ZMod (m / 2))) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hcc : k.val = 1
  · refine ⟨((1 : Nat) : ZMod (m / 2)), 0, by omega, ?_⟩
    have hts : (((1 : Nat) : ZMod (m / 2))).val = 1 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 1 m (((1 : Nat) : ZMod (m / 2)))).val = 1 := by
      rw [iota_val hm, hts]
      apply iota1_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have hit : (sigF 1 m)^[0] (iota 1 m (((1 : Nat) : ZMod (m / 2))))
        = iota 1 m (((1 : Nat) : ZMod (m / 2))) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hcc : k.val = 2
  · refine ⟨((0 : Nat) : ZMod (m / 2)), 2, by omega, ?_⟩
    have hts : (((0 : Nat) : ZMod (m / 2))).val = 0 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 1 m (((0 : Nat) : ZMod (m / 2)))).val = 0 := by
      rw [iota_val hm, hts]
      apply iota1_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 1 m (iota 1 m (((0 : Nat) : ZMod (m / 2))))).val
        = m + 2 := by
      rw [sigF_val hm he, sigNat_one, v0]
      apply sig1_eq hm he
      exact Or.inl ⟨by omega, by omega⟩
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((0 : Nat) : ZMod (m / 2)))))).val
        = 2 := by
      rw [sigF_val hm he, sigNat_one, v1]
      apply sig1_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))
    have hit : (sigF 1 m)^[2] (iota 1 m (((0 : Nat) : ZMod (m / 2))))
        = sigF 1 m (sigF 1 m (iota 1 m (((0 : Nat) : ZMod (m / 2))))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hcc : k.val = 3
  · refine ⟨((1 : Nat) : ZMod (m / 2)), 2, by omega, ?_⟩
    have hts : (((1 : Nat) : ZMod (m / 2))).val = 1 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 1 m (((1 : Nat) : ZMod (m / 2)))).val = 1 := by
      rw [iota_val hm, hts]
      apply iota1_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 1 m (iota 1 m (((1 : Nat) : ZMod (m / 2))))).val
        = m + 3 := by
      rw [sigF_val hm he, sigNat_one, v0]
      apply sig1_eq hm he
      exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((1 : Nat) : ZMod (m / 2)))))).val
        = 3 := by
      rw [sigF_val hm he, sigNat_one, v1]
      apply sig1_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))
    have hit : (sigF 1 m)^[2] (iota 1 m (((1 : Nat) : ZMod (m / 2))))
        = sigF 1 m (sigF 1 m (iota 1 m (((1 : Nat) : ZMod (m / 2))))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hcc : k.val ≤ m / 2
  · refine ⟨((k.val - 2 : Nat) : ZMod (m / 2)), 2, by omega, ?_⟩
    have hts : (((k.val - 2 : Nat) : ZMod (m / 2))).val = k.val - 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 1 m (((k.val - 2 : Nat) : ZMod (m / 2)))).val = m + 2 * (k.val - 2) := by
      rw [iota_val hm, hts]
      apply iota1_eq hm
      exact Or.inr (⟨by omega, by omega⟩)
    have v1 : (sigF 1 m (iota 1 m (((k.val - 2 : Nat) : ZMod (m / 2))))).val
        = m + 2 * (k.val - 2) + 1 := by
      rw [sigF_val hm he, sigNat_one, v0]
      apply sig1_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)))))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((k.val - 2 : Nat) : ZMod (m / 2)))))).val
        = k.val := by
      rw [sigF_val hm he, sigNat_one, v1]
      apply sig1_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega⟩))))))))
    have hit : (sigF 1 m)^[2] (iota 1 m (((k.val - 2 : Nat) : ZMod (m / 2))))
        = sigF 1 m (sigF 1 m (iota 1 m (((k.val - 2 : Nat) : ZMod (m / 2))))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hcc : k.val = m / 2 + 1
  · refine ⟨((m / 2 - 1 : Nat) : ZMod (m / 2)), 2, by omega, ?_⟩
    have hts : (((m / 2 - 1 : Nat) : ZMod (m / 2))).val = m / 2 - 1 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 1 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))).val = 2 * m - 2 := by
      rw [iota_val hm, hts]
      apply iota1_eq hm
      exact Or.inr (⟨by omega, by omega⟩)
    have v1 : (sigF 1 m (iota 1 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))).val
        = 2 * m - 1 := by
      rw [sigF_val hm he, sigNat_one, v0]
      apply sig1_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)))))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))))).val
        = m / 2 + 1 := by
      rw [sigF_val hm he, sigNat_one, v1]
      apply sig1_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))
    have hit : (sigF 1 m)^[2] (iota 1 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))
        = sigF 1 m (sigF 1 m (iota 1 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hcc : k.val = m / 2 + 2
  · refine ⟨((m / 2 - 1 : Nat) : ZMod (m / 2)), 3, by omega, ?_⟩
    have hts : (((m / 2 - 1 : Nat) : ZMod (m / 2))).val = m / 2 - 1 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 1 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))).val = 2 * m - 2 := by
      rw [iota_val hm, hts]
      apply iota1_eq hm
      exact Or.inr (⟨by omega, by omega⟩)
    have v1 : (sigF 1 m (iota 1 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))).val
        = 2 * m - 1 := by
      rw [sigF_val hm he, sigNat_one, v0]
      apply sig1_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)))))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))))).val
        = m / 2 + 1 := by
      rw [sigF_val hm he, sigNat_one, v1]
      apply sig1_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))))).val
        = m / 2 + 2 := by
      rw [sigF_val hm he, sigNat_one, v2]
      apply sig1_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    have hit : (sigF 1 m)^[3] (iota 1 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))
        = sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hcc : k.val = m / 2 + 3
  · refine ⟨((0 : Nat) : ZMod (m / 2)), 3, by omega, ?_⟩
    have hts : (((0 : Nat) : ZMod (m / 2))).val = 0 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 1 m (((0 : Nat) : ZMod (m / 2)))).val = 0 := by
      rw [iota_val hm, hts]
      apply iota1_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 1 m (iota 1 m (((0 : Nat) : ZMod (m / 2))))).val
        = m + 2 := by
      rw [sigF_val hm he, sigNat_one, v0]
      apply sig1_eq hm he
      exact Or.inl ⟨by omega, by omega⟩
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((0 : Nat) : ZMod (m / 2)))))).val
        = 2 := by
      rw [sigF_val hm he, sigNat_one, v1]
      apply sig1_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((0 : Nat) : ZMod (m / 2))))))).val
        = m / 2 + 3 := by
      rw [sigF_val hm he, sigNat_one, v2]
      apply sig1_eq hm he
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
    have hit : (sigF 1 m)^[3] (iota 1 m (((0 : Nat) : ZMod (m / 2))))
        = sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((0 : Nat) : ZMod (m / 2)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hcc : k.val = m / 2 + 4
  · refine ⟨((1 : Nat) : ZMod (m / 2)), 3, by omega, ?_⟩
    have hts : (((1 : Nat) : ZMod (m / 2))).val = 1 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 1 m (((1 : Nat) : ZMod (m / 2)))).val = 1 := by
      rw [iota_val hm, hts]
      apply iota1_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 1 m (iota 1 m (((1 : Nat) : ZMod (m / 2))))).val
        = m + 3 := by
      rw [sigF_val hm he, sigNat_one, v0]
      apply sig1_eq hm he
      exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((1 : Nat) : ZMod (m / 2)))))).val
        = 3 := by
      rw [sigF_val hm he, sigNat_one, v1]
      apply sig1_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((1 : Nat) : ZMod (m / 2))))))).val
        = m / 2 + 4 := by
      rw [sigF_val hm he, sigNat_one, v2]
      apply sig1_eq hm he
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
    have hit : (sigF 1 m)^[3] (iota 1 m (((1 : Nat) : ZMod (m / 2))))
        = sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((1 : Nat) : ZMod (m / 2)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hcc : k.val ≤ m + 1
  · refine ⟨((k.val - m / 2 - 3 : Nat) : ZMod (m / 2)), 3, by omega, ?_⟩
    have hts : (((k.val - m / 2 - 3 : Nat) : ZMod (m / 2))).val = k.val - m / 2 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 1 m (((k.val - m / 2 - 3 : Nat) : ZMod (m / 2)))).val = m + 2 * (k.val - m / 2 - 3) := by
      rw [iota_val hm, hts]
      apply iota1_eq hm
      exact Or.inr (⟨by omega, by omega⟩)
    have v1 : (sigF 1 m (iota 1 m (((k.val - m / 2 - 3 : Nat) : ZMod (m / 2))))).val
        = m + 2 * (k.val - m / 2 - 3) + 1 := by
      rw [sigF_val hm he, sigNat_one, v0]
      apply sig1_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)))))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((k.val - m / 2 - 3 : Nat) : ZMod (m / 2)))))).val
        = k.val - m / 2 - 1 := by
      rw [sigF_val hm he, sigNat_one, v1]
      apply sig1_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega⟩))))))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((k.val - m / 2 - 3 : Nat) : ZMod (m / 2))))))).val
        = k.val := by
      rw [sigF_val hm he, sigNat_one, v2]
      apply sig1_eq hm he
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
    have hit : (sigF 1 m)^[3] (iota 1 m (((k.val - m / 2 - 3 : Nat) : ZMod (m / 2))))
        = sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((k.val - m / 2 - 3 : Nat) : ZMod (m / 2)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hcc : k.val = m + 2
  · refine ⟨((0 : Nat) : ZMod (m / 2)), 1, by omega, ?_⟩
    have hts : (((0 : Nat) : ZMod (m / 2))).val = 0 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 1 m (((0 : Nat) : ZMod (m / 2)))).val = 0 := by
      rw [iota_val hm, hts]
      apply iota1_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 1 m (iota 1 m (((0 : Nat) : ZMod (m / 2))))).val
        = m + 2 := by
      rw [sigF_val hm he, sigNat_one, v0]
      apply sig1_eq hm he
      exact Or.inl ⟨by omega, by omega⟩
    have hit : (sigF 1 m)^[1] (iota 1 m (((0 : Nat) : ZMod (m / 2))))
        = sigF 1 m (iota 1 m (((0 : Nat) : ZMod (m / 2)))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hcc : k.val = m + 3
  · refine ⟨((1 : Nat) : ZMod (m / 2)), 1, by omega, ?_⟩
    have hts : (((1 : Nat) : ZMod (m / 2))).val = 1 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 1 m (((1 : Nat) : ZMod (m / 2)))).val = 1 := by
      rw [iota_val hm, hts]
      apply iota1_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 1 m (iota 1 m (((1 : Nat) : ZMod (m / 2))))).val
        = m + 3 := by
      rw [sigF_val hm he, sigNat_one, v0]
      apply sig1_eq hm he
      exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    have hit : (sigF 1 m)^[1] (iota 1 m (((1 : Nat) : ZMod (m / 2))))
        = sigF 1 m (iota 1 m (((1 : Nat) : ZMod (m / 2)))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hcc : k.val = 2 * m - 1
  · refine ⟨((m / 2 - 1 : Nat) : ZMod (m / 2)), 1, by omega, ?_⟩
    have hts : (((m / 2 - 1 : Nat) : ZMod (m / 2))).val = m / 2 - 1 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 1 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))).val = 2 * m - 2 := by
      rw [iota_val hm, hts]
      apply iota1_eq hm
      exact Or.inr (⟨by omega, by omega⟩)
    have v1 : (sigF 1 m (iota 1 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))).val
        = 2 * m - 1 := by
      rw [sigF_val hm he, sigNat_one, v0]
      apply sig1_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)))))))
    have hit : (sigF 1 m)^[1] (iota 1 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))
        = sigF 1 m (iota 1 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hcc : k.val % 2 = 0
  · refine ⟨(((k.val - m) / 2 : Nat) : ZMod (m / 2)), 0, by omega, ?_⟩
    have hts : ((((k.val - m) / 2 : Nat) : ZMod (m / 2))).val = (k.val - m) / 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 1 m ((((k.val - m) / 2 : Nat) : ZMod (m / 2)))).val = m + 2 * ((k.val - m) / 2) := by
      rw [iota_val hm, hts]
      apply iota1_eq hm
      exact Or.inr (⟨by omega, by omega⟩)
    have hit : (sigF 1 m)^[0] (iota 1 m ((((k.val - m) / 2 : Nat) : ZMod (m / 2))))
        = iota 1 m ((((k.val - m) / 2 : Nat) : ZMod (m / 2))) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  refine ⟨(((k.val - m - 1) / 2 : Nat) : ZMod (m / 2)), 1, by omega, ?_⟩
  have hts : ((((k.val - m - 1) / 2 : Nat) : ZMod (m / 2))).val = (k.val - m - 1) / 2 :=
    ZMod.val_natCast_of_lt (by omega)
  have v0 : (iota 1 m ((((k.val - m - 1) / 2 : Nat) : ZMod (m / 2)))).val = m + 2 * ((k.val - m - 1) / 2) := by
    rw [iota_val hm, hts]
    apply iota1_eq hm
    exact Or.inr (⟨by omega, by omega⟩)
  have v1 : (sigF 1 m (iota 1 m ((((k.val - m - 1) / 2 : Nat) : ZMod (m / 2))))).val
      = k.val := by
    rw [sigF_val hm he, sigNat_one, v0]
    apply sig1_eq hm he
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)))))))
  have hit : (sigF 1 m)^[1] (iota 1 m ((((k.val - m - 1) / 2 : Nat) : ZMod (m / 2))))
      = sigF 1 m (iota 1 m ((((k.val - m - 1) / 2 : Nat) : ZMod (m / 2)))) := rfl
  refine Fin.ext ?_
  rw [hit, v1]
  all_goals omega

set_option maxHeartbeats 1600000 in
private theorem cover2 {m : Nat} [NeZero m] [NeZero (m / 2)]
    (hm : 8 ≤ m) (he : m % 2 = 0) (k : Fin (2 * m)) :
    ∃ t : ZMod (m / 2), ∃ j : Nat, j < 4 ∧ (sigF 2 m)^[j] (iota 2 m t) = k := by
  have hk := k.isLt
  by_cases hcc : k.val = 1
  · refine ⟨((m / 2 - 2 : Nat) : ZMod (m / 2)), 3, by omega, ?_⟩
    have hts : (((m / 2 - 2 : Nat) : ZMod (m / 2))).val = m / 2 - 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 2 m (((m / 2 - 2 : Nat) : ZMod (m / 2)))).val = m - 4 := by
      rw [iota_val hm, hts]
      apply iota2_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 2 m (iota 2 m (((m / 2 - 2 : Nat) : ZMod (m / 2))))).val
        = m + m / 2 - 2 := by
      rw [sigF_val hm he, sigNat_two, v0]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 2 - 2 : Nat) : ZMod (m / 2)))))).val
        = m + m / 2 - 1 := by
      rw [sigF_val hm he, sigNat_two, v1]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 2 - 2 : Nat) : ZMod (m / 2))))))).val
        = 1 := by
      rw [sigF_val hm he, sigNat_two, v2]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))))
    have hit : (sigF 2 m)^[3] (iota 2 m (((m / 2 - 2 : Nat) : ZMod (m / 2))))
        = sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 2 - 2 : Nat) : ZMod (m / 2)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hcc : k.val = 3
  · refine ⟨((m / 2 - 1 : Nat) : ZMod (m / 2)), 3, by omega, ?_⟩
    have hts : (((m / 2 - 1 : Nat) : ZMod (m / 2))).val = m / 2 - 1 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 2 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))).val = 2 * m - 1 := by
      rw [iota_val hm, hts]
      apply iota2_eq hm
      exact Or.inr (⟨by omega, by omega⟩)
    have v1 : (sigF 2 m (iota 2 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))).val
        = m - 1 := by
      rw [sigF_val hm he, sigNat_two, v0]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))))).val
        = m + m / 2 := by
      rw [sigF_val hm he, sigNat_two, v1]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))))).val
        = 3 := by
      rw [sigF_val hm he, sigNat_two, v2]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))))
    have hit : (sigF 2 m)^[3] (iota 2 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))
        = sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hcc : k.val = 5
  · refine ⟨((0 : Nat) : ZMod (m / 2)), 3, by omega, ?_⟩
    have hts : (((0 : Nat) : ZMod (m / 2))).val = 0 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 2 m (((0 : Nat) : ZMod (m / 2)))).val = 0 := by
      rw [iota_val hm, hts]
      apply iota2_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 2 m (iota 2 m (((0 : Nat) : ZMod (m / 2))))).val
        = m := by
      rw [sigF_val hm he, sigNat_two, v0]
      apply sig2_eq hm he
      exact Or.inl ⟨by omega, by omega⟩
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((0 : Nat) : ZMod (m / 2)))))).val
        = m + m / 2 + 1 := by
      rw [sigF_val hm he, sigNat_two, v1]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((0 : Nat) : ZMod (m / 2))))))).val
        = 5 := by
      rw [sigF_val hm he, sigNat_two, v2]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))))
    have hit : (sigF 2 m)^[3] (iota 2 m (((0 : Nat) : ZMod (m / 2))))
        = sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((0 : Nat) : ZMod (m / 2)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hcc : k.val ≤ m - 3 ∧ k.val % 2 = 0
  · refine ⟨((k.val / 2 : Nat) : ZMod (m / 2)), 0, by omega, ?_⟩
    have hts : (((k.val / 2 : Nat) : ZMod (m / 2))).val = k.val / 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 2 m (((k.val / 2 : Nat) : ZMod (m / 2)))).val = 2 * (k.val / 2) := by
      rw [iota_val hm, hts]
      apply iota2_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have hit : (sigF 2 m)^[0] (iota 2 m (((k.val / 2 : Nat) : ZMod (m / 2))))
        = iota 2 m (((k.val / 2 : Nat) : ZMod (m / 2))) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hcc : k.val ≤ m - 3
  · refine ⟨(((k.val - 5) / 2 : Nat) : ZMod (m / 2)), 3, by omega, ?_⟩
    have hts : ((((k.val - 5) / 2 : Nat) : ZMod (m / 2))).val = (k.val - 5) / 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 2 m ((((k.val - 5) / 2 : Nat) : ZMod (m / 2)))).val = 2 * ((k.val - 5) / 2) := by
      rw [iota_val hm, hts]
      apply iota2_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 2 m (iota 2 m ((((k.val - 5) / 2 : Nat) : ZMod (m / 2))))).val
        = (k.val - 5) / 2 + m := by
      rw [sigF_val hm he, sigNat_two, v0]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m ((((k.val - 5) / 2 : Nat) : ZMod (m / 2)))))).val
        = (k.val - 5) / 2 + m + m / 2 + 1 := by
      rw [sigF_val hm he, sigNat_two, v1]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m ((((k.val - 5) / 2 : Nat) : ZMod (m / 2))))))).val
        = k.val := by
      rw [sigF_val hm he, sigNat_two, v2]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))))
    have hit : (sigF 2 m)^[3] (iota 2 m ((((k.val - 5) / 2 : Nat) : ZMod (m / 2))))
        = sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m ((((k.val - 5) / 2 : Nat) : ZMod (m / 2)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hcc : k.val = m - 2
  · refine ⟨((m / 2 - 3 : Nat) : ZMod (m / 2)), 3, by omega, ?_⟩
    have hts : (((m / 2 - 3 : Nat) : ZMod (m / 2))).val = m / 2 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 2 m (((m / 2 - 3 : Nat) : ZMod (m / 2)))).val = m - 6 := by
      rw [iota_val hm, hts]
      apply iota2_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 2 m (iota 2 m (((m / 2 - 3 : Nat) : ZMod (m / 2))))).val
        = m + m / 2 - 3 := by
      rw [sigF_val hm he, sigNat_two, v0]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 2 - 3 : Nat) : ZMod (m / 2)))))).val
        = 2 * m - 2 := by
      rw [sigF_val hm he, sigNat_two, v1]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 2 - 3 : Nat) : ZMod (m / 2))))))).val
        = m - 2 := by
      rw [sigF_val hm he, sigNat_two, v2]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))))))
    have hit : (sigF 2 m)^[3] (iota 2 m (((m / 2 - 3 : Nat) : ZMod (m / 2))))
        = sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 2 - 3 : Nat) : ZMod (m / 2)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hcc : k.val = m - 1
  · refine ⟨((m / 2 - 1 : Nat) : ZMod (m / 2)), 1, by omega, ?_⟩
    have hts : (((m / 2 - 1 : Nat) : ZMod (m / 2))).val = m / 2 - 1 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 2 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))).val = 2 * m - 1 := by
      rw [iota_val hm, hts]
      apply iota2_eq hm
      exact Or.inr (⟨by omega, by omega⟩)
    have v1 : (sigF 2 m (iota 2 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))).val
        = m - 1 := by
      rw [sigF_val hm he, sigNat_two, v0]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))))))
    have hit : (sigF 2 m)^[1] (iota 2 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))
        = sigF 2 m (iota 2 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hcc : k.val = m
  · refine ⟨((0 : Nat) : ZMod (m / 2)), 1, by omega, ?_⟩
    have hts : (((0 : Nat) : ZMod (m / 2))).val = 0 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 2 m (((0 : Nat) : ZMod (m / 2)))).val = 0 := by
      rw [iota_val hm, hts]
      apply iota2_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 2 m (iota 2 m (((0 : Nat) : ZMod (m / 2))))).val
        = m := by
      rw [sigF_val hm he, sigNat_two, v0]
      apply sig2_eq hm he
      exact Or.inl ⟨by omega, by omega⟩
    have hit : (sigF 2 m)^[1] (iota 2 m (((0 : Nat) : ZMod (m / 2))))
        = sigF 2 m (iota 2 m (((0 : Nat) : ZMod (m / 2)))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hcc : k.val ≤ m + m / 2 - 2
  · refine ⟨((k.val - m : Nat) : ZMod (m / 2)), 1, by omega, ?_⟩
    have hts : (((k.val - m : Nat) : ZMod (m / 2))).val = k.val - m :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 2 m (((k.val - m : Nat) : ZMod (m / 2)))).val = 2 * (k.val - m) := by
      rw [iota_val hm, hts]
      apply iota2_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 2 m (iota 2 m (((k.val - m : Nat) : ZMod (m / 2))))).val
        = k.val := by
      rw [sigF_val hm he, sigNat_two, v0]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))
    have hit : (sigF 2 m)^[1] (iota 2 m (((k.val - m : Nat) : ZMod (m / 2))))
        = sigF 2 m (iota 2 m (((k.val - m : Nat) : ZMod (m / 2)))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hcc : k.val = m + m / 2 - 1
  · refine ⟨((m / 2 - 2 : Nat) : ZMod (m / 2)), 2, by omega, ?_⟩
    have hts : (((m / 2 - 2 : Nat) : ZMod (m / 2))).val = m / 2 - 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 2 m (((m / 2 - 2 : Nat) : ZMod (m / 2)))).val = m - 4 := by
      rw [iota_val hm, hts]
      apply iota2_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 2 m (iota 2 m (((m / 2 - 2 : Nat) : ZMod (m / 2))))).val
        = m + m / 2 - 2 := by
      rw [sigF_val hm he, sigNat_two, v0]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 2 - 2 : Nat) : ZMod (m / 2)))))).val
        = m + m / 2 - 1 := by
      rw [sigF_val hm he, sigNat_two, v1]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))))
    have hit : (sigF 2 m)^[2] (iota 2 m (((m / 2 - 2 : Nat) : ZMod (m / 2))))
        = sigF 2 m (sigF 2 m (iota 2 m (((m / 2 - 2 : Nat) : ZMod (m / 2))))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hcc : k.val = m + m / 2
  · refine ⟨((m / 2 - 1 : Nat) : ZMod (m / 2)), 2, by omega, ?_⟩
    have hts : (((m / 2 - 1 : Nat) : ZMod (m / 2))).val = m / 2 - 1 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 2 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))).val = 2 * m - 1 := by
      rw [iota_val hm, hts]
      apply iota2_eq hm
      exact Or.inr (⟨by omega, by omega⟩)
    have v1 : (sigF 2 m (iota 2 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))).val
        = m - 1 := by
      rw [sigF_val hm he, sigNat_two, v0]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))))).val
        = m + m / 2 := by
      rw [sigF_val hm he, sigNat_two, v1]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))
    have hit : (sigF 2 m)^[2] (iota 2 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))
        = sigF 2 m (sigF 2 m (iota 2 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hcc : k.val = m + m / 2 + 1
  · refine ⟨((0 : Nat) : ZMod (m / 2)), 2, by omega, ?_⟩
    have hts : (((0 : Nat) : ZMod (m / 2))).val = 0 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 2 m (((0 : Nat) : ZMod (m / 2)))).val = 0 := by
      rw [iota_val hm, hts]
      apply iota2_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 2 m (iota 2 m (((0 : Nat) : ZMod (m / 2))))).val
        = m := by
      rw [sigF_val hm he, sigNat_two, v0]
      apply sig2_eq hm he
      exact Or.inl ⟨by omega, by omega⟩
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((0 : Nat) : ZMod (m / 2)))))).val
        = m + m / 2 + 1 := by
      rw [sigF_val hm he, sigNat_two, v1]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))
    have hit : (sigF 2 m)^[2] (iota 2 m (((0 : Nat) : ZMod (m / 2))))
        = sigF 2 m (sigF 2 m (iota 2 m (((0 : Nat) : ZMod (m / 2))))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hcc : k.val ≤ 2 * m - 3
  · refine ⟨((k.val - m - m / 2 - 1 : Nat) : ZMod (m / 2)), 2, by omega, ?_⟩
    have hts : (((k.val - m - m / 2 - 1 : Nat) : ZMod (m / 2))).val = k.val - m - m / 2 - 1 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 2 m (((k.val - m - m / 2 - 1 : Nat) : ZMod (m / 2)))).val = 2 * (k.val - m - m / 2 - 1) := by
      rw [iota_val hm, hts]
      apply iota2_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 2 m (iota 2 m (((k.val - m - m / 2 - 1 : Nat) : ZMod (m / 2))))).val
        = k.val - m / 2 - 1 := by
      rw [sigF_val hm he, sigNat_two, v0]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((k.val - m - m / 2 - 1 : Nat) : ZMod (m / 2)))))).val
        = k.val := by
      rw [sigF_val hm he, sigNat_two, v1]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))
    have hit : (sigF 2 m)^[2] (iota 2 m (((k.val - m - m / 2 - 1 : Nat) : ZMod (m / 2))))
        = sigF 2 m (sigF 2 m (iota 2 m (((k.val - m - m / 2 - 1 : Nat) : ZMod (m / 2))))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hcc : k.val = 2 * m - 2
  · refine ⟨((m / 2 - 3 : Nat) : ZMod (m / 2)), 2, by omega, ?_⟩
    have hts : (((m / 2 - 3 : Nat) : ZMod (m / 2))).val = m / 2 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have v0 : (iota 2 m (((m / 2 - 3 : Nat) : ZMod (m / 2)))).val = m - 6 := by
      rw [iota_val hm, hts]
      apply iota2_eq hm
      exact Or.inl ⟨by omega, by omega⟩
    have v1 : (sigF 2 m (iota 2 m (((m / 2 - 3 : Nat) : ZMod (m / 2))))).val
        = m + m / 2 - 3 := by
      rw [sigF_val hm he, sigNat_two, v0]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 2 - 3 : Nat) : ZMod (m / 2)))))).val
        = 2 * m - 2 := by
      rw [sigF_val hm he, sigNat_two, v1]
      apply sig2_eq hm he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))
    have hit : (sigF 2 m)^[2] (iota 2 m (((m / 2 - 3 : Nat) : ZMod (m / 2))))
        = sigF 2 m (sigF 2 m (iota 2 m (((m / 2 - 3 : Nat) : ZMod (m / 2))))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  refine ⟨((m / 2 - 1 : Nat) : ZMod (m / 2)), 0, by omega, ?_⟩
  have hts : (((m / 2 - 1 : Nat) : ZMod (m / 2))).val = m / 2 - 1 :=
    ZMod.val_natCast_of_lt (by omega)
  have v0 : (iota 2 m (((m / 2 - 1 : Nat) : ZMod (m / 2)))).val = 2 * m - 1 := by
    rw [iota_val hm, hts]
    apply iota2_eq hm
    exact Or.inr (⟨by omega, by omega⟩)
  have hit : (sigF 2 m)^[0] (iota 2 m (((m / 2 - 1 : Nat) : ZMod (m / 2))))
      = iota 2 m (((m / 2 - 1 : Nat) : ZMod (m / 2))) := rfl
  refine Fin.ext ?_
  rw [hit, v0]
  all_goals omega

/-- **Level-2 conclusion**: each per-color label successor is a single
`2m`-cycle.  The hypothesis `3 ∤ m` enters exactly here. -/
private theorem sigF_singleCycle {m : Nat} [NeZero m] (hm : 8 ≤ m)
    (he : m % 2 = 0) (h3 : m % 3 ≠ 0) (c : Fin 3) :
    IsSingleCycleMap (sigF c m) := by
  haveI : NeZero (m / 2) := ⟨by omega⟩
  have hcop : Nat.Coprime 3 (m / 2) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_
    intro hdvd
    obtain ⟨c', hc'⟩ := hdvd
    have hm6 : m = 6 * c' := by omega
    refine h3 ?_
    rw [hm6]
    omega
  have hchain : ∀ t : ZMod (m / 2),
      (sigF c m)^[4] (iota c m t) = iota c m (t + 3) := by
    rcases fin3_cases c with rfl | rfl | rfl
    · exact chain0 hm he
    · exact chain1 hm he
    · exact chain2 hm he
  have hcover : ∀ k : Fin (2 * m), ∃ t : ZMod (m / 2), ∃ j : Nat,
      j < 4 ∧ (sigF c m)^[j] (iota c m t) = k := by
    rcases fin3_cases c with rfl | rfl | rfl
    · exact cover0 hm he
    · exact cover1 hm he
    · exact cover2 hm he
  exact single_cycle_of_interval_splice (sigF c m)
    (fun t : ZMod (m / 2) => t + 3) (iota c m) (fun _ => 4)
    (fun _ => Nat.succ_pos 3) hchain (addThree_singleCycle _ hcop) hcover

/-! ## Assembly: the per-color core single cycles -/

section Assembly

/-- The level-1 splice: for even `m ≥ 8` with `3 ∤ m` the core map
`G_c = T_{u_c} ∘ ρ_c` is a single `m²`-cycle on `Q_m`. -/
private theorem coreMap_singleCycle {m : Nat} [NeZero m] (hm : 8 ≤ m)
    (he : m % 2 = 0) (h3 : m % 3 ≠ 0) (c : Fin 3) :
    IsSingleCycleMap (coreMap c m) := by
  have hspec : ∀ k, SpecAt c m k := by
    rcases fin3_cases c with rfl | rfl | rfl
    · exact spec0 hm he
    · exact spec1 hm he
    · exact spec2 hm he
  have hhit : ∀ w : TerminalQ m, ∃ j : Nat,
      activePred c (w + j • uVec m c) := by
    rcases fin3_cases c with rfl | rfl | rfl
    · exact hit0 hm he
    · exact hit1 hm he
    · exact hit2 hm he
  exact single_cycle_of_interval_splice (coreMap c m) (sigF c m)
    (headF c m) (fun k => lenNat c m k.val) (lenF_pos hm he c)
    (traverse_of_spec hm he c hspec)
    (sigF_singleCycle hm he h3 c)
    (cover_of_spec hm he c hspec (sigF_singleCycle hm he h3 c).1.2 hhit)

/-! ### The `m = 4` orbit certificate

The only even `3 ∤ m` modulus below `8`.  The three orbit rank tables are
the `G_c`-orbits of `(0,0)` printed by
`scripts/search_d3_even_dir.py core3free --m 4` (index `4x + y`). -/

private def rankTbl4 : Fin 3 → List (ZMod 16)
  | 0 => [0, 7, 1, 15, 9, 10, 8, 2, 3, 13, 11, 12, 6, 4, 14, 5]
  | 1 => [0, 12, 5, 14, 9, 2, 4, 7, 15, 11, 13, 6, 1, 10, 3, 8]
  | 2 => [0, 13, 10, 7, 11, 4, 1, 14, 2, 8, 15, 5, 9, 6, 12, 3]

private def rank4 (c : Fin 3) (w : TerminalQ 4) : ZMod 16 :=
  (rankTbl4 c).getD (w.1.val * 4 + w.2.val) 0

private theorem core4_singleCycle (c : Fin 3) :
    IsSingleCycleMap
      (fun w : TerminalQ 4 => rho c w + driftPair 4 c) := by
  refine Shared.single_cycle_of_zmod_rank _ (rank4 c) ?_ ?_ <;>
    rcases fin3_cases c with rfl | rfl | rfl <;> decide

/-- The pair-coordinate core statement, all even `m ≥ 4` with `3 ∤ m`. -/
private theorem corePair_singleCycle {m : Nat} [NeZero m] (hm : 4 ≤ m)
    (hEven : Even m) (h3 : m % 3 ≠ 0) (c : Fin 3) :
    IsSingleCycleMap
      (fun w : TerminalQ m => rho c w + driftPair m c) := by
  have he : m % 2 = 0 := Nat.even_iff.mp hEven
  by_cases h4 : m = 4
  · subst h4
    exact core4_singleCycle c
  · have hm8 : 8 ≤ m := by omega
    have hcm : (fun w : TerminalQ m => rho c w + driftPair m c)
        = coreMap c m := by
      funext w
      show rho c w + driftPair m c = rho c w + uVec m c
      rw [driftPair_eq_uVec hm h3 c]
    rw [hcm]
    exact coreMap_singleCycle hm8 he h3 c

end Assembly

/-! ## The root-section core statement -/

/-- **The `3 ∤ m` core cyclicity** (module 3a deliverable): for every even
`m ≥ 4` with `3 ∤ m` and every color, the conjugated core map
`w ↦ ρ_c(w) + u_c` of the rail-seam schedule is a single `m²`-cycle on the
standard root section.  Feeds `railReturn_singleCycle_of_core` /
`railCycleData` of module 2.

Hypothesis audit: `3 ∤ m` is used for the drift table (`driftPair` branches
on `m % 3`) and for level 2 (`+3` generates `ZMod (m/2)`); evenness is used
by the parity branches of the label successor, the size `m/2` of the
level-2 transversal and the parity arguments in the ray analysis; `4 ≤ m`
fixes the seam geometry (module 1) and `m = 4`, `m = 6` are the excluded
small cases (`m = 6` is void here since `3 ∣ 6`). -/
theorem railCore_singleCycle_of_not_dvd (m : Nat) [NeZero m] (hm : 4 ≤ m)
    (hEven : Even m) (h3 : m % 3 ≠ 0) (c : Fin 3) :
    Shared.IsSingleCycleMap
      (fun w : RootState m => rhoRoot c w + driftVec m c) := by
  refine Shared.single_cycle_of_equiv_conj (rootPairEquiv m).symm
    (fun w : RootState m => rhoRoot c w + driftVec m c)
    (fun q : TerminalQ m => rho c q + driftPair m c)
    (corePair_singleCycle hm hEven h3 c) ?_
  intro q
  show rootPair (rhoRoot c (pairRoot q) + driftVec m c)
      = rho c q + driftPair m c
  rw [show rhoRoot c (pairRoot q) = pairRoot (rho c q) from by
      show pairRoot (rho c (rootPair (pairRoot q))) = _
      rw [rootPair_pairRoot],
    show driftVec m c = pairRoot (driftPair m c) from rfl,
    ← pairRoot_add, rootPair_pairRoot]

/-- The three core inputs of `railCycleData`, packaged. -/
def railCycleData_of_not_dvd (m : Nat) [NeZero m] (hm : 4 ≤ m)
    (hEven : Even m) (h3 : m % 3 ≠ 0) :
    RootFlatCycle.RootFlatCycleData 2 m :=
  railCycleData m hm
    (railCore_singleCycle_of_not_dvd m hm hEven h3 0)
    (railCore_singleCycle_of_not_dvd m hm hEven h3 1)
    (railCore_singleCycle_of_not_dvd m hm hEven h3 2)

/-! ## Decide anchors

The closed-form label successor and length tables against
`scripts/search_d3_even_dir.py core3free --m {8,10}` (the script is ground
truth). -/

section Anchors

example : (List.range 16).map (sig0 8)
    = [5, 6, 3, 9, 11, 13, 14, 15, 0, 10, 1, 12, 2, 7, 8, 4] := by decide

example : (List.range 16).map (len0 8)
    = [4, 4, 8, 3, 2, 1, 1, 1, 1, 8, 2, 8, 3, 7, 7, 4] := by decide

example : (List.range 16).map (sig1 8)
    = [10, 11, 7, 8, 9, 6, 12, 14, 0, 1, 2, 3, 13, 4, 15, 5] := by decide

example : (List.range 16).map (len1 8)
    = [7, 7, 4, 4, 4, 8, 3, 2, 1, 1, 1, 1, 8, 2, 8, 3] := by decide

example : (List.range 16).map (sig2 8)
    = [8, 2, 9, 4, 10, 15, 0, 12, 13, 14, 11, 1, 3, 5, 6, 7] := by decide

example : (List.range 16).map (len2 8)
    = [1, 8, 2, 8, 3, 7, 7, 4, 4, 4, 8, 3, 2, 1, 1, 1] := by decide

example : (List.range 20).map (sig0 10)
    = [6, 7, 8, 4, 11, 13, 15, 17, 18, 19, 0, 12, 1, 14, 2, 16, 3, 9,
      10, 5] := by decide

example : (List.range 20).map (len0 10)
    = [5, 5, 5, 10, 4, 3, 2, 1, 1, 1, 1, 10, 2, 10, 3, 10, 4, 9, 9,
      5] := by decide

example : (List.range 20).map (sig1 10)
    = [12, 13, 8, 9, 10, 11, 7, 14, 16, 18, 0, 1, 2, 3, 15, 4, 17, 5,
      19, 6] := by decide

example : (List.range 20).map (sig2 10)
    = [10, 2, 11, 4, 12, 6, 13, 19, 0, 15, 16, 17, 18, 14, 1, 3, 5, 7,
      8, 9] := by decide

-- Sample of the `m = 4` rank step: the full step law is part of
-- `core4_singleCycle` above.
example :
    rank4 0 (rho 0 ((0 : ZMod 4), (0 : ZMod 4)) + driftPair 4 0) = 1 ∧
      rank4 1 (rho 1 ((2 : ZMod 4), (3 : ZMod 4)) + driftPair 4 1)
        = rank4 1 ((2 : ZMod 4), (3 : ZMod 4)) + 1 := by decide

end Anchors



end D3EvenRailCore3Free
end V28Hard
end EvenV11
