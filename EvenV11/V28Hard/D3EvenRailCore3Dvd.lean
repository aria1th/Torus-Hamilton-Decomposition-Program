import EvenV11.V28Hard.D3EvenRailSchedule
import EvenV11.V28Hard.TerminalA2IntervalSplice

/-!
# D3-even rail seam: the core cyclicity, case `3 ∣ m` (module 3b)

This file proves the three per-color core statements of the rail-seam
schedule for even `m ≥ 4` with `3 ∣ m`
(`docs/WILDE_SEARCH_20260610.md` §4 item 4; numeric ground truth:
`scripts/search_d3_even_dir.py construct` / `core3dvd`):

* **`railCore_singleCycle_of_dvd`**: for every color `c`, the conjugated
  core map `w ↦ rhoRoot c w + driftVec m c` is a single `m²`-cycle on the
  standard root section `Fin 2 → ZMod m`.

Together with `D3EvenRailSchedule.railCycleData` this closes RF3 for the
rail-seam schedule in the `3 ∣ m` case; combined with the `3 ∤ m` module
`D3EvenRailCore3Free` it covers every even `m ≥ 4`.

The proof mirrors module 3a: a two-level interval splice (engine:
`TerminalA2IntervalSplice.single_cycle_of_interval_splice`), entirely in the
manuscript pair coordinates `TerminalQ m`, bridged to the root section at
the very end through `rootPairEquiv`:

* **Level 1** (points): the core map `G_c = T_{u_c} ∘ ρ_c` with the `3 ∣ m`
  drifts `u = ((m−4,1), (3,m−4), (1,3))` translates until the orbit hits the
  active seam, then `ρ_c` kicks it one seam rank forward.  Interval `k`
  starts at `head k = seamPoint c (k+1) + u_c`, has the explicit length
  `lenNat c m k`, and ends one kick after `seamPoint c (σ_c k)`.  The label
  successor `σ_c = sigNat c m` and the lengths are closed-form piecewise
  affine maps, organized around `d = m/3` (verified against the script for
  all even `3 ∣ m` moduli up to `60`; the three colors are rank rotations of
  each other by `+3` and `+m`).
* **Level 2** (labels): `σ_c` is spliced along the `(m/3 − 1)`-element
  transversal `ι_c` (the low labels with `d−4` and `d−1` skipped, shifted by
  the per-color offset `0 / 3 / m`), with interval lengths
  `(6, …, 6, 11, 7, 7, 6, 5)`: the first return of `σ_c` to the transversal
  is exactly `+2` on `ZMod (m/3 − 1)`, and `+2` is a single cycle precisely
  because `m` is even (`d = m/3` is even, so `m/3 − 1` is odd) — this is
  where evenness enters; `3 ∣ m` enters through the drift table and the
  mod-3 residue classes of the label successor.

The generic argument needs `m ≥ 18` for level 2 and `m ≥ 12` for level 1;
`m = 12` closes level 2 by an explicit `24`-label orbit-rank certificate and
`m = 6` is closed by an explicit `36`-point orbit-rank certificate, both by
`decide`.  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace EvenV11
namespace V28Hard
namespace D3EvenRailCore3Dvd

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

/-- Six-range value table for casts below `6m` (the `u₀`/`u₁` rays add up
to `4m` to a sub-`2m` head coordinate). -/
private theorem val_cases6m {a : Nat} (h : a < 6 * m) :
    (a < m ∧ ((a : Nat) : ZMod m).val = a) ∨
      (m ≤ a ∧ a < 2 * m ∧ ((a : Nat) : ZMod m).val = a - m) ∨
      (2 * m ≤ a ∧ a < 3 * m ∧ ((a : Nat) : ZMod m).val = a - 2 * m) ∨
      (3 * m ≤ a ∧ a < 4 * m ∧ ((a : Nat) : ZMod m).val = a - 3 * m) ∨
      (4 * m ≤ a ∧ a < 5 * m ∧ ((a : Nat) : ZMod m).val = a - 4 * m) ∨
      (5 * m ≤ a ∧ ((a : Nat) : ZMod m).val = a - 5 * m) := by
  rcases Nat.lt_or_ge a (4 * m) with h4 | h4
  · rcases val_cases4m h4 with h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h'.1, by omega, h'.2⟩)))
  rcases Nat.lt_or_ge a (5 * m) with h5 | h5
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h4, h5, ?_⟩))))
    rw [castShift 4 (show a = (a - 4 * m) + 4 * m by omega)]
    exact valNat_lt (by omega)
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h5, ?_⟩))))
    rw [castShift 5 (show a = (a - 5 * m) + 5 * m by omega)]
    exact valNat_lt (by omega)

/-- Uniform cast congruence: equality up to an explicit multiple of `m`
(in either direction, up to `5m`), dischargeable by `omega`. -/
private theorem castMod {a b : Nat}
    (h : a = b ∨ a = b + 1 * m ∨ a = b + 2 * m ∨ a = b + 3 * m ∨
      a = b + 4 * m ∨ a = b + 5 * m ∨
      b = a + 1 * m ∨ b = a + 2 * m ∨ b = a + 3 * m ∨
      b = a + 4 * m ∨ b = a + 5 * m) :
    ((a : Nat) : ZMod m) = ((b : Nat) : ZMod m) := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · rw [h]
  · exact castShift 1 h
  · exact castShift 2 h
  · exact castShift 3 h
  · exact castShift 4 h
  · exact castShift 5 h
  · exact (castShift 1 h).symm
  · exact (castShift 2 h).symm
  · exact (castShift 3 h).symm
  · exact (castShift 4 h).symm
  · exact (castShift 5 h).symm

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

/-- The three conjugated drifts for `3 ∣ m`, in `cpt` form:
`u₀ = (m−4, 1)`, `u₁ = (3, m−4)`, `u₂ = (1, 3)`. -/
private def uVec (m : Nat) [NeZero m] : Fin 3 → TerminalQ m
  | 0 => cpt (m - 4) 1
  | 1 => cpt 3 (m - 4)
  | 2 => cpt 1 3

private theorem cpt_add_u0 (hm : 12 ≤ m) (a b : Nat) :
    ∀ j : Nat, j ≤ m → (cpt a b : TerminalQ m) + j • uVec m 0
      = cpt (a + 4 * (m - j)) (b + j)
  | 0, _ => by
      rw [zero_nsmul, add_zero, Nat.add_zero]
      exact cpt_congr (castShift (a := a + 4 * (m - 0)) 4 (by omega)).symm
        rfl
  | j + 1, hj => by
      rw [succ_nsmul, ← add_assoc, cpt_add_u0 hm a b j (by omega)]
      show (cpt (a + 4 * (m - j)) (b + j) : TerminalQ m)
          + cpt (m - 4) 1 = _
      rw [cpt_add]
      exact cpt_congr (castShift 1 (by omega)) (castShift 0 (by omega))

private theorem cpt_add_u1 (hm : 12 ≤ m) (a b : Nat) :
    ∀ j : Nat, j ≤ m → (cpt a b : TerminalQ m) + j • uVec m 1
      = cpt (a + 3 * j) (b + 4 * (m - j))
  | 0, _ => by
      rw [zero_nsmul, add_zero]
      exact cpt_congr (castShift (a := a) (b := a + 3 * 0) 0 (by omega))
        (castShift (a := b + 4 * (m - 0)) 4 (by omega)).symm
  | j + 1, hj => by
      rw [succ_nsmul, ← add_assoc, cpt_add_u1 hm a b j (by omega)]
      show (cpt (a + 3 * j) (b + 4 * (m - j)) : TerminalQ m)
          + cpt 3 (m - 4) = _
      rw [cpt_add]
      exact cpt_congr (castShift 0 (by omega)) (castShift 1 (by omega))

private theorem cpt_add_u2 (hm : 12 ≤ m) (a b : Nat) :
    ∀ j : Nat, (cpt a b : TerminalQ m) + j • uVec m 2
      = cpt (a + j) (b + 3 * j)
  | 0 => by
      rw [zero_nsmul, add_zero]
      exact cpt_congr (castShift (a := a) (b := a + 0) 0 (by omega))
        (castShift (a := b) (b := b + 3 * 0) 0 (by omega))
  | j + 1 => by
      rw [succ_nsmul, ← add_assoc, cpt_add_u2 hm a b j]
      show (cpt (a + j) (b + 3 * j) : TerminalQ m) + cpt 1 3 = _
      rw [cpt_add]
      exact cpt_congr (castShift 0 (by omega)) (castShift 0 (by omega))

private theorem fin3_cases (c : Fin 3) : c = 0 ∨ c = 1 ∨ c = 2 := by
  revert c
  decide

/-- The conjugated drift table of module 2 in `cpt` form, case `3 ∣ m`. -/
private theorem driftPair_eq_uVec (hm : 4 ≤ m) (h3 : m % 3 = 0)
    (c : Fin 3) : driftPair m c = uVec m c := by
  rcases fin3_cases c with rfl | rfl | rfl
  · rw [driftPair_dvd_zero h3]
    show _ = (cpt (m - 4) 1 : TerminalQ m)
    unfold cpt
    rw [Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    push_cast
    ring
  · rw [driftPair_dvd_one h3]
    show _ = (cpt 3 (m - 4) : TerminalQ m)
    unfold cpt
    rw [Prod.mk.injEq]
    refine ⟨?_, rfl⟩
    push_cast
    ring
  · rw [driftPair_dvd_two h3]
    show _ = (cpt 1 3 : TerminalQ m)
    unfold cpt
    rw [Prod.mk.injEq]
    constructor <;> (push_cast; ring)

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

/-! ## The label successor `σ_c` and the interval lengths

All guards are written additively (`k + c ≤ …`) so that no branch is
distorted by `Nat` subtraction at small `m`.  `d` abbreviates `m / 3`. -/

/-- Label successor table, color 0 (`3 ∣ m`, even `m ≥ 12`). -/
def sig0 (m k : Nat) : Nat :=
  if k + 3 ≤ 2 * (m / 3) then k + m / 3 + 1
  else if k + 2 = 2 * (m / 3) then m / 3 - 1
  else if k + 3 ≤ m then 4 * m - 7 - 3 * k
  else if k + 2 = m then m + 3
  else if k + 1 = m then m
  else if k = m then m + 1
  else if k = m + 2 then m - 1
  else if k + 6 = 2 * m then 2 * m - 1
  else if k + 2 = 2 * m then 2 * m - 5
  else if k + 1 = 2 * m then m / 3
  else if k % 3 = 1 then (2 * m - 5 - k) / 3
  else k + 1

/-- Interval length table, color 0. -/
def len0 (m k : Nat) : Nat :=
  if k + 3 ≤ 2 * (m / 3) then m / 3
  else if k + 2 = 2 * (m / 3) then 2 * (m / 3)
  else if k + 3 ≤ m then m - 2 - k
  else if k + 2 = m then 1
  else if k + 1 = m then m
  else if k = m then m
  else if k = m + 2 then m - 1
  else if k + 6 = 2 * m then 1
  else if k + 2 = 2 * m then m - 1
  else if k + 1 = 2 * m then m / 3
  else if k % 3 = 1 then (2 * m - 2 - k) / 3
  else m

/-- Label successor table, color 1 (the `+3` rank rotation of color 0).
The low/high split keeps the `if` tower shallow enough for `split_ifs`. -/
def sig1 (m k : Nat) : Nat :=
  if k ≤ m then
    (if k = 0 then 1
     else if k = 1 then 2 * m - 2
     else if k = 2 then m / 3 + 3
     else if k ≤ 2 * (m / 3) then k + m / 3 + 1
     else if k = 2 * (m / 3) + 1 then m / 3 + 2
     else 4 * m + 5 - 3 * k)
  else
    (if k = m + 1 then m + 6
     else if k = m + 2 then m + 3
     else if k = m + 3 then m + 4
     else if k = m + 5 then m + 2
     else if k + 3 = 2 * m then 2
     else if k + 1 = 2 * m then 0
     else if k % 3 = 1 then (2 * m - 2 - k) / 3 + 3
     else k + 1)

/-- Interval length table, color 1. -/
def len1 (m k : Nat) : Nat :=
  if k ≤ m then
    (if k = 0 then m
     else if k = 1 then m - 1
     else if k = 2 then m / 3
     else if k ≤ 2 * (m / 3) then m / 3
     else if k = 2 * (m / 3) + 1 then 2 * (m / 3)
     else m + 1 - k)
  else
    (if k = m + 1 then 1
     else if k = m + 2 then m
     else if k = m + 3 then m
     else if k = m + 5 then m - 1
     else if k + 3 = 2 * m then 1
     else if k + 1 = 2 * m then m
     else if k % 3 = 1 then (2 * m + 1 - k) / 3
     else m)

/-- Label successor table, color 2 (the `+m` rank rotation of color 0). -/
def sig2 (m k : Nat) : Nat :=
  if k = 0 then 1
  else if k = 2 then 2 * m - 1
  else if k + 6 = m then m - 1
  else if k + 2 = m then m - 5
  else if k + 1 = m then m + m / 3
  else if k + 3 ≤ m then
    (if k % 3 = 1 then (m - 5 - k) / 3 + m else k + 1)
  else if k + 3 ≤ 2 * (m / 3) + m then k + m / 3 + 1
  else if k + 2 = 2 * (m / 3) + m then m + m / 3 - 1
  else if k + 3 ≤ 2 * m then 6 * m - 7 - 3 * k
  else if k + 2 = 2 * m then 3
  else 0

/-- Interval length table, color 2. -/
def len2 (m k : Nat) : Nat :=
  if k = 0 then m
  else if k = 2 then m - 1
  else if k + 6 = m then 1
  else if k + 2 = m then m - 1
  else if k + 1 = m then m / 3
  else if k + 3 ≤ m then
    (if k % 3 = 1 then (m - 2 - k) / 3 else m)
  else if k + 3 ≤ 2 * (m / 3) + m then m / 3
  else if k + 2 = 2 * (m / 3) + m then 2 * (m / 3)
  else if k + 3 ≤ 2 * m then 2 * m - 2 - k
  else if k + 2 = 2 * m then 1
  else m

section SigBounds

set_option maxHeartbeats 3200000 in
private theorem sig0_lt {m k : Nat} (hm : 12 ≤ m) (he : m % 2 = 0)
    (h3 : m % 3 = 0) (hk : k < 2 * m) : sig0 m k < 2 * m := by
  unfold sig0
  split_ifs <;> omega

set_option maxHeartbeats 3200000 in
private theorem sig1_lt {m k : Nat} (hm : 12 ≤ m) (he : m % 2 = 0)
    (h3 : m % 3 = 0) (hk : k < 2 * m) : sig1 m k < 2 * m := by
  unfold sig1
  split_ifs <;> omega

set_option maxHeartbeats 3200000 in
private theorem sig2_lt {m k : Nat} (hm : 12 ≤ m) (he : m % 2 = 0)
    (h3 : m % 3 = 0) (hk : k < 2 * m) : sig2 m k < 2 * m := by
  unfold sig2
  split_ifs <;> omega

set_option maxHeartbeats 3200000 in
private theorem len0_pos {m k : Nat} (hm : 12 ≤ m) (he : m % 2 = 0)
    (h3 : m % 3 = 0) (hk : k < 2 * m) : 0 < len0 m k := by
  unfold len0
  split_ifs <;> omega

set_option maxHeartbeats 3200000 in
private theorem len1_pos {m k : Nat} (hm : 12 ≤ m) (he : m % 2 = 0)
    (h3 : m % 3 = 0) (hk : k < 2 * m) : 0 < len1 m k := by
  unfold len1
  split_ifs <;> omega

set_option maxHeartbeats 3200000 in
private theorem len2_pos {m k : Nat} (hm : 12 ≤ m) (he : m % 2 = 0)
    (h3 : m % 3 = 0) (hk : k < 2 * m) : 0 < len2 m k := by
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

private theorem sigF_val {m : Nat} (hm : 12 ≤ m) (he : m % 2 = 0)
    (h3 : m % 3 = 0) (c : Fin 3) (k : Fin (2 * m)) :
    (sigF c m k).val = sigNat c m k.val := by
  have hk := k.isLt
  refine Nat.mod_eq_of_lt ?_
  fin_cases c
  · exact sig0_lt hm he h3 hk
  · exact sig1_lt hm he h3 hk
  · exact sig2_lt hm he h3 hk

private theorem lenF_pos {m : Nat} (hm : 12 ≤ m) (he : m % 2 = 0)
    (h3 : m % 3 = 0) (c : Fin 3) (k : Fin (2 * m)) :
    0 < lenNat c m k.val := by
  have hk := k.isLt
  fin_cases c
  · exact len0_pos hm he h3 hk
  · exact len1_pos hm he h3 hk
  · exact len2_pos hm he h3 hk

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
private theorem traverse_of_spec (hm : 12 ≤ m) (he : m % 2 = 0)
    (h3 : m % 3 = 0) (c : Fin 3)
    (hspec : ∀ k, SpecAt c m k) (k : Fin (2 * m)) :
    (coreMap c m)^[lenNat c m k.val] (headF c m k)
      = headF c m (sigF c m k) := by
  obtain ⟨hin, hhit⟩ := hspec k
  obtain ⟨J, hJ⟩ : ∃ J, lenNat c m k.val = J + 1 :=
    ⟨lenNat c m k.val - 1, by have := lenF_pos hm he h3 c k; omega⟩
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
private theorem cover_of_spec (hm : 12 ≤ m) (he : m % 2 = 0)
    (h3 : m % 3 = 0) (c : Fin 3)
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
  have hlen := lenF_pos hm he h3 c k
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

set_option maxHeartbeats 3200000 in
private theorem sig0_eq {m k v : Nat} (hm : 12 ≤ m) (he : m % 2 = 0)
    (h3 : m % 3 = 0)
    (h : (k + 3 ≤ 2 * (m / 3) ∧ v = k + m / 3 + 1) ∨
      (k + 2 = 2 * (m / 3) ∧ v = m / 3 - 1) ∨
      (2 * (m / 3) ≤ k + 1 ∧ k + 3 ≤ m ∧ v = 4 * m - 7 - 3 * k) ∨
      (k + 2 = m ∧ v = m + 3) ∨ (k + 1 = m ∧ v = m) ∨
      (k = m ∧ v = m + 1) ∨ (k = m + 2 ∧ v = m - 1) ∨
      (k + 6 = 2 * m ∧ v = 2 * m - 1) ∨
      (k + 2 = 2 * m ∧ v = 2 * m - 5) ∨
      (k + 1 = 2 * m ∧ v = m / 3) ∨
      (m + 1 ≤ k ∧ k + 5 ≤ 2 * m ∧ k % 3 = 1 ∧
        v = (2 * m - 5 - k) / 3) ∨
      (m + 3 ≤ k ∧ k + 3 ≤ 2 * m ∧ k % 3 ≠ 1 ∧ k + 6 ≠ 2 * m ∧
        v = k + 1)) :
    sig0 m k = v := by
  unfold sig0
  split_ifs <;> omega

set_option maxHeartbeats 3200000 in
private theorem len0_eq {m k v : Nat} (hm : 12 ≤ m) (he : m % 2 = 0)
    (h3 : m % 3 = 0)
    (h : (k + 3 ≤ 2 * (m / 3) ∧ v = m / 3) ∨
      (k + 2 = 2 * (m / 3) ∧ v = 2 * (m / 3)) ∨
      (2 * (m / 3) ≤ k + 1 ∧ k + 3 ≤ m ∧ v = m - 2 - k) ∨
      (k + 2 = m ∧ v = 1) ∨ (k + 1 = m ∧ v = m) ∨
      (k = m ∧ v = m) ∨ (k = m + 2 ∧ v = m - 1) ∨
      (k + 6 = 2 * m ∧ v = 1) ∨
      (k + 2 = 2 * m ∧ v = m - 1) ∨
      (k + 1 = 2 * m ∧ v = m / 3) ∨
      (m + 1 ≤ k ∧ k + 5 ≤ 2 * m ∧ k % 3 = 1 ∧
        v = (2 * m - 2 - k) / 3) ∨
      (m + 3 ≤ k ∧ k + 3 ≤ 2 * m ∧ k % 3 ≠ 1 ∧ k + 6 ≠ 2 * m ∧
        v = m)) :
    len0 m k = v := by
  unfold len0
  split_ifs <;> omega

set_option maxHeartbeats 3200000 in
private theorem sig1_eq {m k v : Nat} (hm : 12 ≤ m) (he : m % 2 = 0)
    (h3 : m % 3 = 0)
    (h : (k = 0 ∧ v = 1) ∨ (k = 1 ∧ v = 2 * m - 2) ∨
      (k = 2 ∧ v = m / 3 + 3) ∨
      (3 ≤ k ∧ k ≤ 2 * (m / 3) ∧ v = k + m / 3 + 1) ∨
      (k = 2 * (m / 3) + 1 ∧ v = m / 3 + 2) ∨
      (2 * (m / 3) + 2 ≤ k ∧ k ≤ m ∧ v = 4 * m + 5 - 3 * k) ∨
      (k = m + 1 ∧ v = m + 6) ∨ (k = m + 2 ∧ v = m + 3) ∨
      (k = m + 3 ∧ v = m + 4) ∨ (k = m + 5 ∧ v = m + 2) ∨
      (k + 3 = 2 * m ∧ v = 2) ∨ (k + 1 = 2 * m ∧ v = 0) ∨
      (m + 4 ≤ k ∧ k + 2 ≤ 2 * m ∧ k % 3 = 1 ∧
        v = (2 * m - 2 - k) / 3 + 3) ∨
      (m + 6 ≤ k ∧ k + 4 ≤ 2 * m ∧ k % 3 ≠ 1 ∧ k + 3 ≠ 2 * m ∧
        v = k + 1)) :
    sig1 m k = v := by
  unfold sig1
  split_ifs <;> omega

set_option maxHeartbeats 3200000 in
private theorem len1_eq {m k v : Nat} (hm : 12 ≤ m) (he : m % 2 = 0)
    (h3 : m % 3 = 0)
    (h : (k = 0 ∧ v = m) ∨ (k = 1 ∧ v = m - 1) ∨
      (k = 2 ∧ v = m / 3) ∨
      (3 ≤ k ∧ k ≤ 2 * (m / 3) ∧ v = m / 3) ∨
      (k = 2 * (m / 3) + 1 ∧ v = 2 * (m / 3)) ∨
      (2 * (m / 3) + 2 ≤ k ∧ k ≤ m ∧ v = m + 1 - k) ∨
      (k = m + 1 ∧ v = 1) ∨ (k = m + 2 ∧ v = m) ∨
      (k = m + 3 ∧ v = m) ∨ (k = m + 5 ∧ v = m - 1) ∨
      (k + 3 = 2 * m ∧ v = 1) ∨ (k + 1 = 2 * m ∧ v = m) ∨
      (m + 4 ≤ k ∧ k + 2 ≤ 2 * m ∧ k % 3 = 1 ∧
        v = (2 * m + 1 - k) / 3) ∨
      (m + 6 ≤ k ∧ k + 4 ≤ 2 * m ∧ k % 3 ≠ 1 ∧ k + 3 ≠ 2 * m ∧
        v = m)) :
    len1 m k = v := by
  unfold len1
  split_ifs <;> omega

set_option maxHeartbeats 3200000 in
private theorem sig2_eq {m k v : Nat} (hm : 12 ≤ m) (he : m % 2 = 0)
    (h3 : m % 3 = 0)
    (h : (k = 0 ∧ v = 1) ∨ (k = 2 ∧ v = 2 * m - 1) ∨
      (k + 6 = m ∧ v = m - 1) ∨ (k + 2 = m ∧ v = m - 5) ∨
      (k + 1 = m ∧ v = m + m / 3) ∨
      (1 ≤ k ∧ k + 3 ≤ m ∧ k % 3 = 1 ∧ v = (m - 5 - k) / 3 + m) ∨
      (1 ≤ k ∧ k + 3 ≤ m ∧ k % 3 ≠ 1 ∧ k ≠ 2 ∧ k + 6 ≠ m ∧
        v = k + 1) ∨
      (m ≤ k ∧ k + 3 ≤ 2 * (m / 3) + m ∧ v = k + m / 3 + 1) ∨
      (k + 2 = 2 * (m / 3) + m ∧ v = m + m / 3 - 1) ∨
      (2 * (m / 3) + m ≤ k + 1 ∧ k + 3 ≤ 2 * m ∧
        v = 6 * m - 7 - 3 * k) ∨
      (k + 2 = 2 * m ∧ v = 3) ∨ (k + 1 = 2 * m ∧ v = 0)) :
    sig2 m k = v := by
  unfold sig2
  split_ifs <;> omega

set_option maxHeartbeats 3200000 in
private theorem len2_eq {m k v : Nat} (hm : 12 ≤ m) (he : m % 2 = 0)
    (h3 : m % 3 = 0)
    (h : (k = 0 ∧ v = m) ∨ (k = 2 ∧ v = m - 1) ∨
      (k + 6 = m ∧ v = 1) ∨ (k + 2 = m ∧ v = m - 1) ∨
      (k + 1 = m ∧ v = m / 3) ∨
      (1 ≤ k ∧ k + 3 ≤ m ∧ k % 3 = 1 ∧ v = (m - 2 - k) / 3) ∨
      (1 ≤ k ∧ k + 3 ≤ m ∧ k % 3 ≠ 1 ∧ k ≠ 2 ∧ k + 6 ≠ m ∧
        v = m) ∨
      (m ≤ k ∧ k + 3 ≤ 2 * (m / 3) + m ∧ v = m / 3) ∨
      (k + 2 = 2 * (m / 3) + m ∧ v = 2 * (m / 3)) ∨
      (2 * (m / 3) + m ≤ k + 1 ∧ k + 3 ≤ 2 * m ∧
        v = 2 * m - 2 - k) ∨
      (k + 2 = 2 * m ∧ v = 1) ∨ (k + 1 = 2 * m ∧ v = m)) :
    len2 m k = v := by
  unfold len2
  split_ifs <;> omega

end TableEval

/-! ## The interval specifications, color by color -/

section Specs

set_option maxHeartbeats 3200000 in
private theorem spec0 {m : Nat} [NeZero m] (hm : 12 ≤ m)
    (he : m % 2 = 0) (h3 : m % 3 = 0) (k : Fin (2 * m)) :
    SpecAt 0 m k := by
  have hk := k.isLt
  have hm4 : 4 ≤ m := by omega
  by_cases hB1 : k.val + 3 ≤ 2 * (m / 3)
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 0 m k = (cpt (2 * m - 5 - k.val) (k.val + 2) : TerminalQ m) := by
      show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
      rw [hs, sp0_anti hm4 (by omega)]
      rw [show (uVec m 0 : TerminalQ m) = cpt (m - 4) 1 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig0 m k.val = k.val + m / 3 + 1 :=
      sig0_eq hm he h3 (Or.inl (⟨by omega, by omega⟩))
    have hlen : len0 m k.val = m / 3 :=
      len0_eq hm he h3 (Or.inl (⟨by omega, by omega⟩))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_zero, hlen] at hi
      rw [hhead, cpt_add_u0 hm _ _ i (by omega)]
      intro hact
      have hval := active0_cpt hm4 hact
      have hx := val_cases6m (m := m)
        (a := 2 * m - 5 - k.val + 4 * (m - i)) (by omega)
      have hy := val_cases4m (m := m)
        (a := k.val + 2 + i) (by omega)
      omega
    · rw [lenNat_zero, hlen, hhead,
        cpt_add_u0 hm _ _ (m / 3 - 1) (by omega)]
      show _ = seamPoint0Nat m (sigF 0 m k).val
      rw [sigF_val hm he h3 0 k, sigNat_zero, hsig,
        sp0_anti hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hB2 : k.val + 2 = 2 * (m / 3)
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 0 m k = (cpt (2 * m - 5 - k.val) (k.val + 2) : TerminalQ m) := by
      show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
      rw [hs, sp0_anti hm4 (by omega)]
      rw [show (uVec m 0 : TerminalQ m) = cpt (m - 4) 1 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig0 m k.val = m / 3 - 1 :=
      sig0_eq hm he h3 (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    have hlen : len0 m k.val = 2 * (m / 3) :=
      len0_eq hm he h3 (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_zero, hlen] at hi
      rw [hhead, cpt_add_u0 hm _ _ i (by omega)]
      intro hact
      have hval := active0_cpt hm4 hact
      have hx := val_cases6m (m := m)
        (a := 2 * m - 5 - k.val + 4 * (m - i)) (by omega)
      have hy := val_cases4m (m := m)
        (a := k.val + 2 + i) (by omega)
      omega
    · rw [lenNat_zero, hlen, hhead,
        cpt_add_u0 hm _ _ (2 * (m / 3) - 1) (by omega)]
      show _ = seamPoint0Nat m (sigF 0 m k).val
      rw [sigF_val hm he h3 0 k, sigNat_zero, hsig,
        sp0_anti hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hB3 : k.val + 3 ≤ m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 0 m k = (cpt (2 * m - 5 - k.val) (k.val + 2) : TerminalQ m) := by
      show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
      rw [hs, sp0_anti hm4 (by omega)]
      rw [show (uVec m 0 : TerminalQ m) = cpt (m - 4) 1 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig0 m k.val = 4 * m - 7 - 3 * k.val :=
      sig0_eq hm he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have hlen : len0 m k.val = m - 2 - k.val :=
      len0_eq hm he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_zero, hlen] at hi
      rw [hhead, cpt_add_u0 hm _ _ i (by omega)]
      intro hact
      have hval := active0_cpt hm4 hact
      have hx := val_cases6m (m := m)
        (a := 2 * m - 5 - k.val + 4 * (m - i)) (by omega)
      have hy := val_cases4m (m := m)
        (a := k.val + 2 + i) (by omega)
      omega
    · rw [lenNat_zero, hlen, hhead,
        cpt_add_u0 hm _ _ (m - 2 - k.val - 1) (by omega)]
      show _ = seamPoint0Nat m (sigF 0 m k).val
      rw [sigF_val hm he h3 0 k, sigNat_zero, hsig,
        sp0_row hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hB4 : k.val + 2 = m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 0 m k = (cpt (m - 3) (m - 1) : TerminalQ m) := by
      show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
      rw [hs, sp0_mid hm4 (by omega)]
      rw [show (uVec m 0 : TerminalQ m) = cpt (m - 4) 1 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig0 m k.val = m + 3 :=
      sig0_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    have hlen : len0 m k.val = 1 :=
      len0_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_zero, hlen] at hi
      rw [hhead, cpt_add_u0 hm _ _ i (by omega)]
      intro hact
      have hval := active0_cpt hm4 hact
      have hx := val_cases6m (m := m)
        (a := m - 3 + 4 * (m - i)) (by omega)
      have hy := val_cases4m (m := m)
        (a := m - 1 + i) (by omega)
      omega
    · rw [lenNat_zero, hlen, hhead,
        cpt_add_u0 hm _ _ (1 - 1) (by omega)]
      show _ = seamPoint0Nat m (sigF 0 m k).val
      rw [sigF_val hm he h3 0 k, sigNat_zero, hsig,
        sp0_row hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hB5 : k.val + 1 = m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 0 m k = (cpt (2 * m - 4) (m) : TerminalQ m) := by
      show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
      rw [hs, sp0_row hm4 (by omega) (by omega)]
      rw [show (uVec m 0 : TerminalQ m) = cpt (m - 4) 1 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig0 m k.val = m :=
      sig0_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    have hlen : len0 m k.val = m :=
      len0_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_zero, hlen] at hi
      rw [hhead, cpt_add_u0 hm _ _ i (by omega)]
      intro hact
      have hval := active0_cpt hm4 hact
      have hx := val_cases6m (m := m)
        (a := 2 * m - 4 + 4 * (m - i)) (by omega)
      have hy := val_cases4m (m := m)
        (a := m + i) (by omega)
      omega
    · rw [lenNat_zero, hlen, hhead,
        cpt_add_u0 hm _ _ (m - 1) (by omega)]
      show _ = seamPoint0Nat m (sigF 0 m k).val
      rw [sigF_val hm he h3 0 k, sigNat_zero, hsig,
        sp0_row hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hB6 : k.val = m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 0 m k = (cpt (2 * m - 5) (m) : TerminalQ m) := by
      show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
      rw [hs, sp0_row hm4 (by omega) (by omega)]
      rw [show (uVec m 0 : TerminalQ m) = cpt (m - 4) 1 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig0 m k.val = m + 1 :=
      sig0_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))
    have hlen : len0 m k.val = m :=
      len0_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_zero, hlen] at hi
      rw [hhead, cpt_add_u0 hm _ _ i (by omega)]
      intro hact
      have hval := active0_cpt hm4 hact
      have hx := val_cases6m (m := m)
        (a := 2 * m - 5 + 4 * (m - i)) (by omega)
      have hy := val_cases4m (m := m)
        (a := m + i) (by omega)
      omega
    · rw [lenNat_zero, hlen, hhead,
        cpt_add_u0 hm _ _ (m - 1) (by omega)]
      show _ = seamPoint0Nat m (sigF 0 m k).val
      rw [sigF_val hm he h3 0 k, sigNat_zero, hsig,
        sp0_row hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hB7 : k.val = m + 2
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 0 m k = (cpt (2 * m - 7) (m) : TerminalQ m) := by
      show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
      rw [hs, sp0_row hm4 (by omega) (by omega)]
      rw [show (uVec m 0 : TerminalQ m) = cpt (m - 4) 1 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig0 m k.val = m - 1 :=
      sig0_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))
    have hlen : len0 m k.val = m - 1 :=
      len0_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_zero, hlen] at hi
      rw [hhead, cpt_add_u0 hm _ _ i (by omega)]
      intro hact
      have hval := active0_cpt hm4 hact
      have hx := val_cases6m (m := m)
        (a := 2 * m - 7 + 4 * (m - i)) (by omega)
      have hy := val_cases4m (m := m)
        (a := m + i) (by omega)
      omega
    · rw [lenNat_zero, hlen, hhead,
        cpt_add_u0 hm _ _ (m - 1 - 1) (by omega)]
      show _ = seamPoint0Nat m (sigF 0 m k).val
      rw [sigF_val hm he h3 0 k, sigNat_zero, hsig,
        sp0_mid hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hB8 : k.val + 6 = 2 * m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 0 m k = (cpt (m + 1) (m) : TerminalQ m) := by
      show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
      rw [hs, sp0_row hm4 (by omega) (by omega)]
      rw [show (uVec m 0 : TerminalQ m) = cpt (m - 4) 1 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig0 m k.val = 2 * m - 1 :=
      sig0_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))
    have hlen : len0 m k.val = 1 :=
      len0_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_zero, hlen] at hi
      rw [hhead, cpt_add_u0 hm _ _ i (by omega)]
      intro hact
      have hval := active0_cpt hm4 hact
      have hx := val_cases6m (m := m)
        (a := m + 1 + 4 * (m - i)) (by omega)
      have hy := val_cases4m (m := m)
        (a := m + i) (by omega)
      omega
    · rw [lenNat_zero, hlen, hhead,
        cpt_add_u0 hm _ _ (1 - 1) (by omega)]
      show _ = seamPoint0Nat m (sigF 0 m k).val
      rw [sigF_val hm he h3 0 k, sigNat_zero, hsig,
        sp0_last hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hB9 : k.val + 2 = 2 * m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 0 m k = (cpt (m - 3) (1) : TerminalQ m) := by
      show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
      rw [hs, sp0_last hm4 (by omega)]
      rw [show (uVec m 0 : TerminalQ m) = cpt (m - 4) 1 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig0 m k.val = 2 * m - 5 :=
      sig0_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))
    have hlen : len0 m k.val = m - 1 :=
      len0_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_zero, hlen] at hi
      rw [hhead, cpt_add_u0 hm _ _ i (by omega)]
      intro hact
      have hval := active0_cpt hm4 hact
      have hx := val_cases6m (m := m)
        (a := m - 3 + 4 * (m - i)) (by omega)
      have hy := val_cases4m (m := m)
        (a := 1 + i) (by omega)
      omega
    · rw [lenNat_zero, hlen, hhead,
        cpt_add_u0 hm _ _ (m - 1 - 1) (by omega)]
      show _ = seamPoint0Nat m (sigF 0 m k).val
      rw [sigF_val hm he h3 0 k, sigNat_zero, hsig,
        sp0_row hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hB10 : k.val + 1 = 2 * m
  · have hs : (seamSucc m k).val = 0 :=
      seamSucc_val_last (by omega)
    have hhead : headF 0 m k = (cpt (2 * m - 4) (1) : TerminalQ m) := by
      show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
      rw [hs, sp0_anti hm4 (by omega)]
      rw [show (uVec m 0 : TerminalQ m) = cpt (m - 4) 1 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig0 m k.val = m / 3 :=
      sig0_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))))
    have hlen : len0 m k.val = m / 3 :=
      len0_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_zero, hlen] at hi
      rw [hhead, cpt_add_u0 hm _ _ i (by omega)]
      intro hact
      have hval := active0_cpt hm4 hact
      have hx := val_cases6m (m := m)
        (a := 2 * m - 4 + 4 * (m - i)) (by omega)
      have hy := val_cases4m (m := m)
        (a := 1 + i) (by omega)
      omega
    · rw [lenNat_zero, hlen, hhead,
        cpt_add_u0 hm _ _ (m / 3 - 1) (by omega)]
      show _ = seamPoint0Nat m (sigF 0 m k).val
      rw [sigF_val hm he h3 0 k, sigNat_zero, hsig,
        sp0_anti hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hB11 : k.val % 3 = 1
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 0 m k = (cpt (3 * m - 5 - k.val) (m) : TerminalQ m) := by
      show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
      rw [hs, sp0_row hm4 (by omega) (by omega)]
      rw [show (uVec m 0 : TerminalQ m) = cpt (m - 4) 1 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig0 m k.val = (2 * m - 5 - k.val) / 3 :=
      sig0_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))
    have hlen : len0 m k.val = (2 * m - 2 - k.val) / 3 :=
      len0_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_zero, hlen] at hi
      rw [hhead, cpt_add_u0 hm _ _ i (by omega)]
      intro hact
      have hval := active0_cpt hm4 hact
      have hx := val_cases6m (m := m)
        (a := 3 * m - 5 - k.val + 4 * (m - i)) (by omega)
      have hy := val_cases4m (m := m)
        (a := m + i) (by omega)
      omega
    · rw [lenNat_zero, hlen, hhead,
        cpt_add_u0 hm _ _ ((2 * m - 2 - k.val) / 3 - 1) (by omega)]
      show _ = seamPoint0Nat m (sigF 0 m k).val
      rw [sigF_val hm he h3 0 k, sigNat_zero, hsig,
        sp0_anti hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hB12a : k.val + 4 ≤ 2 * m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 0 m k = (cpt (3 * m - 5 - k.val) (m) : TerminalQ m) := by
      show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
      rw [hs, sp0_row hm4 (by omega) (by omega)]
      rw [show (uVec m 0 : TerminalQ m) = cpt (m - 4) 1 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig0 m k.val = k.val + 1 :=
      sig0_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have hlen : len0 m k.val = m :=
      len0_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_zero, hlen] at hi
      rw [hhead, cpt_add_u0 hm _ _ i (by omega)]
      intro hact
      have hval := active0_cpt hm4 hact
      have hx := val_cases6m (m := m)
        (a := 3 * m - 5 - k.val + 4 * (m - i)) (by omega)
      have hy := val_cases4m (m := m)
        (a := m + i) (by omega)
      omega
    · rw [lenNat_zero, hlen, hhead,
        cpt_add_u0 hm _ _ (m - 1) (by omega)]
      show _ = seamPoint0Nat m (sigF 0 m k).val
      rw [sigF_val hm he h3 0 k, sigNat_zero, hsig,
        sp0_row hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  have hs : (seamSucc m k).val = k.val + 1 :=
    seamSucc_val_of_lt (by omega)
  have hhead : headF 0 m k = (cpt (m - 2) (m) : TerminalQ m) := by
    show seamPoint0Nat m (seamSucc m k).val + uVec m 0 = _
    rw [hs, sp0_rowEnd hm4 (by omega)]
    rw [show (uVec m 0 : TerminalQ m) = cpt (m - 4) 1 from rfl,
      cpt_add]
    all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  have hsig : sig0 m k.val = k.val + 1 :=
    sig0_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
  have hlen : len0 m k.val = m :=
    len0_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [lenNat_zero, hlen] at hi
    rw [hhead, cpt_add_u0 hm _ _ i (by omega)]
    intro hact
    have hval := active0_cpt hm4 hact
    have hx := val_cases6m (m := m)
      (a := m - 2 + 4 * (m - i)) (by omega)
    have hy := val_cases4m (m := m)
      (a := m + i) (by omega)
    omega
  · rw [lenNat_zero, hlen, hhead,
      cpt_add_u0 hm _ _ (m - 1) (by omega)]
    show _ = seamPoint0Nat m (sigF 0 m k).val
    rw [sigF_val hm he h3 0 k, sigNat_zero, hsig,
      sp0_rowEnd hm4 (by omega)]
    all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))

set_option maxHeartbeats 3200000 in
private theorem spec1 {m : Nat} [NeZero m] (hm : 12 ≤ m)
    (he : m % 2 = 0) (h3 : m % 3 = 0) (k : Fin (2 * m)) :
    SpecAt 1 m k := by
  have hk := k.isLt
  have hm4 : 4 ≤ m := by omega
  by_cases hC1 : k.val = 0
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (4) (2 * m - 5) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_one hm4 (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt 3 (m - 4) from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = 1 :=
      sig1_eq hm he h3 (Or.inl (⟨by omega, by omega⟩))
    have hlen : len1 m k.val = m :=
      len1_eq hm he h3 (Or.inl (⟨by omega, by omega⟩))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 4 + 3 * i) (by omega)
      have hy := val_cases6m (m := m)
        (a := 2 * m - 5 + 4 * (m - i)) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead,
        cpt_add_u1 hm _ _ (m - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he h3 1 k, sigNat_one, hsig,
        sp1_one hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC2 : k.val = 1
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (4) (2 * m - 6) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_two hm4 (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt 3 (m - 4) from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = 2 * m - 2 :=
      sig1_eq hm he h3 (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    have hlen : len1 m k.val = m - 1 :=
      len1_eq hm he h3 (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 4 + 3 * i) (by omega)
      have hy := val_cases6m (m := m)
        (a := 2 * m - 6 + 4 * (m - i)) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead,
        cpt_add_u1 hm _ _ (m - 1 - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he h3 1 k, sigNat_one, hsig,
        sp1_anti hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC3 : k.val = 2
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (5) (2 * m - 7) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_col hm4 (by omega) (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt 3 (m - 4) from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = m / 3 + 3 :=
      sig1_eq hm he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    have hlen : len1 m k.val = m / 3 :=
      len1_eq hm he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 5 + 3 * i) (by omega)
      have hy := val_cases6m (m := m)
        (a := 2 * m - 7 + 4 * (m - i)) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead,
        cpt_add_u1 hm _ _ (m / 3 - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he h3 1 k, sigNat_one, hsig,
        sp1_col hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC4a : k.val + 1 ≤ 2 * (m / 3)
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (5) (2 * m - 5 - k.val) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_col hm4 (by omega) (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt 3 (m - 4) from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = k.val + m / 3 + 1 :=
      sig1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have hlen : len1 m k.val = m / 3 :=
      len1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 5 + 3 * i) (by omega)
      have hy := val_cases6m (m := m)
        (a := 2 * m - 5 - k.val + 4 * (m - i)) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead,
        cpt_add_u1 hm _ _ (m / 3 - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he h3 1 k, sigNat_one, hsig,
        sp1_col hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC4b : k.val = 2 * (m / 3)
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (5) (2 * m - 5 - k.val) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_col hm4 (by omega) (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt 3 (m - 4) from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = k.val + m / 3 + 1 :=
      sig1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have hlen : len1 m k.val = m / 3 :=
      len1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 5 + 3 * i) (by omega)
      have hy := val_cases6m (m := m)
        (a := 2 * m - 5 - k.val + 4 * (m - i)) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead,
        cpt_add_u1 hm _ _ (m / 3 - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he h3 1 k, sigNat_one, hsig,
        sp1_colEnd hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC5 : k.val = 2 * (m / 3) + 1
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (5) (2 * m - 5 - k.val) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_col hm4 (by omega) (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt 3 (m - 4) from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = m / 3 + 2 :=
      sig1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    have hlen : len1 m k.val = 2 * (m / 3) :=
      len1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 5 + 3 * i) (by omega)
      have hy := val_cases6m (m := m)
        (a := 2 * m - 5 - k.val + 4 * (m - i)) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead,
        cpt_add_u1 hm _ _ (2 * (m / 3) - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he h3 1 k, sigNat_one, hsig,
        sp1_col hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC6a : k.val + 1 ≤ m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (5) (2 * m - 5 - k.val) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_col hm4 (by omega) (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt 3 (m - 4) from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = 4 * m + 5 - 3 * k.val :=
      sig1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have hlen : len1 m k.val = m + 1 - k.val :=
      len1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 5 + 3 * i) (by omega)
      have hy := val_cases6m (m := m)
        (a := 2 * m - 5 - k.val + 4 * (m - i)) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead,
        cpt_add_u1 hm _ _ (m + 1 - k.val - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he h3 1 k, sigNat_one, hsig,
        sp1_anti hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC6b : k.val = m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (5) (2 * m - 5) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_colEnd hm4 (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt 3 (m - 4) from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = 4 * m + 5 - 3 * k.val :=
      sig1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have hlen : len1 m k.val = m + 1 - k.val :=
      len1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 5 + 3 * i) (by omega)
      have hy := val_cases6m (m := m)
        (a := 2 * m - 5 + 4 * (m - i)) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead,
        cpt_add_u1 hm _ _ (m + 1 - k.val - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he h3 1 k, sigNat_one, hsig,
        sp1_anti hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC7 : k.val = m + 1
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (6) (2 * m - 6) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_hop hm4 (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt 3 (m - 4) from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = m + 6 :=
      sig1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))
    have hlen : len1 m k.val = 1 :=
      len1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 6 + 3 * i) (by omega)
      have hy := val_cases6m (m := m)
        (a := 2 * m - 6 + 4 * (m - i)) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead,
        cpt_add_u1 hm _ _ (1 - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he h3 1 k, sigNat_one, hsig,
        sp1_anti hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC8 : k.val = m + 2
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (6) (2 * m - 7) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_anti hm4 (by omega) (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt 3 (m - 4) from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = m + 3 :=
      sig1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))
    have hlen : len1 m k.val = m :=
      len1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 6 + 3 * i) (by omega)
      have hy := val_cases6m (m := m)
        (a := 2 * m - 7 + 4 * (m - i)) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead,
        cpt_add_u1 hm _ _ (m - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he h3 1 k, sigNat_one, hsig,
        sp1_anti hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC9 : k.val = m + 3
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (7) (2 * m - 8) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_anti hm4 (by omega) (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt 3 (m - 4) from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = m + 4 :=
      sig1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))
    have hlen : len1 m k.val = m :=
      len1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 7 + 3 * i) (by omega)
      have hy := val_cases6m (m := m)
        (a := 2 * m - 8 + 4 * (m - i)) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead,
        cpt_add_u1 hm _ _ (m - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he h3 1 k, sigNat_one, hsig,
        sp1_anti hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC10 : k.val = m + 5
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (9) (2 * m - 10) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_anti hm4 (by omega) (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt 3 (m - 4) from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = m + 2 :=
      sig1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))))
    have hlen : len1 m k.val = m - 1 :=
      len1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 9 + 3 * i) (by omega)
      have hy := val_cases6m (m := m)
        (a := 2 * m - 10 + 4 * (m - i)) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead,
        cpt_add_u1 hm _ _ (m - 1 - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he h3 1 k, sigNat_one, hsig,
        sp1_hop hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC11 : k.val + 3 = 2 * m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (m + 1) (m - 2) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_anti hm4 (by omega) (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt 3 (m - 4) from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = 2 :=
      sig1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))))
    have hlen : len1 m k.val = 1 :=
      len1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := m + 1 + 3 * i) (by omega)
      have hy := val_cases6m (m := m)
        (a := m - 2 + 4 * (m - i)) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead,
        cpt_add_u1 hm _ _ (1 - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he h3 1 k, sigNat_one, hsig,
        sp1_two hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC12 : k.val + 1 = 2 * m
  · have hs : (seamSucc m k).val = 0 :=
      seamSucc_val_last (by omega)
    have hhead : headF 1 m k = (cpt (3) (m - 4) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_zero hm4 (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt 3 (m - 4) from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = 0 :=
      sig1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))))))
    have hlen : len1 m k.val = m :=
      len1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 3 + 3 * i) (by omega)
      have hy := val_cases6m (m := m)
        (a := m - 4 + 4 * (m - i)) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead,
        cpt_add_u1 hm _ _ (m - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he h3 1 k, sigNat_one, hsig,
        sp1_zero hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC13 : k.val % 3 = 1
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (k.val + 4 - m) (3 * m - 5 - k.val) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_anti hm4 (by omega) (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt 3 (m - 4) from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = (2 * m - 2 - k.val) / 3 + 3 :=
      sig1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))))
    have hlen : len1 m k.val = (2 * m + 1 - k.val) / 3 :=
      len1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := k.val + 4 - m + 3 * i) (by omega)
      have hy := val_cases6m (m := m)
        (a := 3 * m - 5 - k.val + 4 * (m - i)) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead,
        cpt_add_u1 hm _ _ ((2 * m + 1 - k.val) / 3 - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he h3 1 k, sigNat_one, hsig,
        sp1_col hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hC14a : k.val + 4 ≤ 2 * m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 1 m k = (cpt (k.val + 4 - m) (3 * m - 5 - k.val) : TerminalQ m) := by
      show seamPoint1Nat m (seamSucc m k).val + uVec m 1 = _
      rw [hs, sp1_anti hm4 (by omega) (by omega)]
      rw [show (uVec m 1 : TerminalQ m) = cpt 3 (m - 4) from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig1 m k.val = k.val + 1 :=
      sig1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have hlen : len1 m k.val = m :=
      len1_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_one, hlen] at hi
      rw [hhead, cpt_add_u1 hm _ _ i (by omega)]
      intro hact
      have hval := active1_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := k.val + 4 - m + 3 * i) (by omega)
      have hy := val_cases6m (m := m)
        (a := 3 * m - 5 - k.val + 4 * (m - i)) (by omega)
      omega
    · rw [lenNat_one, hlen, hhead,
        cpt_add_u1 hm _ _ (m - 1) (by omega)]
      show _ = seamPoint1Nat m (sigF 1 m k).val
      rw [sigF_val hm he h3 1 k, sigNat_one, hsig,
        sp1_anti hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  exfalso
  omega

set_option maxHeartbeats 3200000 in
private theorem spec2 {m : Nat} [NeZero m] (hm : 12 ≤ m)
    (he : m % 2 = 0) (h3 : m % 3 = 0) (k : Fin (2 * m)) :
    SpecAt 2 m k := by
  have hk := k.isLt
  have hm4 : 4 ≤ m := by omega
  by_cases hD1 : k.val = 0
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k = (cpt (3) (4) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [hs, sp2_col hm4 (by omega)]
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 3 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = 1 :=
      sig2_eq hm he h3 (Or.inl (⟨by omega, by omega⟩))
    have hlen : len2 m k.val = m :=
      len2_eq hm he h3 (Or.inl (⟨by omega, by omega⟩))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm _ _ i]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 3 + i) (by omega)
      have hy := val_cases4m (m := m)
        (a := 4 + 3 * i) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead,
        cpt_add_u2 hm _ _ (m - 1)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he h3 2 k, sigNat_two, hsig,
        sp2_col hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hD2 : k.val = 2
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k = (cpt (3) (6) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [hs, sp2_col hm4 (by omega)]
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 3 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = 2 * m - 1 :=
      sig2_eq hm he h3 (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    have hlen : len2 m k.val = m - 1 :=
      len2_eq hm he h3 (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm _ _ i]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 3 + i) (by omega)
      have hy := val_cases4m (m := m)
        (a := 6 + 3 * i) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead,
        cpt_add_u2 hm _ _ (m - 1 - 1)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he h3 2 k, sigNat_two, hsig,
        sp2_last hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hD3 : k.val + 6 = m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k = (cpt (3) (m - 2) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [hs, sp2_col hm4 (by omega)]
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 3 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = m - 1 :=
      sig2_eq hm he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    have hlen : len2 m k.val = 1 :=
      len2_eq hm he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm _ _ i]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 3 + i) (by omega)
      have hy := val_cases4m (m := m)
        (a := m - 2 + 3 * i) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead,
        cpt_add_u2 hm _ _ (1 - 1)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he h3 2 k, sigNat_two, hsig,
        sp2_hop hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hD4 : k.val + 2 = m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k = (cpt (4) (m + 1) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [hs, sp2_hop hm4 (by omega)]
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 3 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = m - 5 :=
      sig2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    have hlen : len2 m k.val = m - 1 :=
      len2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm _ _ i]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 4 + i) (by omega)
      have hy := val_cases4m (m := m)
        (a := m + 1 + 3 * i) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead,
        cpt_add_u2 hm _ _ (m - 1 - 1)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he h3 2 k, sigNat_two, hsig,
        sp2_col hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hD5 : k.val + 1 = m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k = (cpt (4) (m + 2) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [hs, sp2_row hm4 (by omega) (by omega)]
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 3 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = m + m / 3 :=
      sig2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    have hlen : len2 m k.val = m / 3 :=
      len2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm _ _ i]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 4 + i) (by omega)
      have hy := val_cases4m (m := m)
        (a := m + 2 + 3 * i) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead,
        cpt_add_u2 hm _ _ (m / 3 - 1)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he h3 2 k, sigNat_two, hsig,
        sp2_row hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hD6a : k.val + 3 ≤ m ∧ k.val % 3 = 1
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k = (cpt (3) (k.val + 4) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [hs, sp2_col hm4 (by omega)]
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 3 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = (m - 5 - k.val) / 3 + m :=
      sig2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩)))))))
    have hlen : len2 m k.val = (m - 2 - k.val) / 3 :=
      len2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩)))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm _ _ i]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 3 + i) (by omega)
      have hy := val_cases4m (m := m)
        (a := k.val + 4 + 3 * i) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead,
        cpt_add_u2 hm _ _ ((m - 2 - k.val) / 3 - 1)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he h3 2 k, sigNat_two, hsig,
        sp2_row hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hD6b : k.val + 3 ≤ m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k = (cpt (3) (k.val + 4) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [hs, sp2_col hm4 (by omega)]
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 3 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = k.val + 1 :=
      sig2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have hlen : len2 m k.val = m :=
      len2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm _ _ i]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 3 + i) (by omega)
      have hy := val_cases4m (m := m)
        (a := k.val + 4 + 3 * i) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead,
        cpt_add_u2 hm _ _ (m - 1)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he h3 2 k, sigNat_two, hsig,
        sp2_col hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hD7a : k.val + 5 ≤ 2 * (m / 3) + m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k = (cpt (k.val + 5 - m) (m + 2) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [hs, sp2_row hm4 (by omega) (by omega)]
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 3 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = k.val + m / 3 + 1 :=
      sig2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have hlen : len2 m k.val = m / 3 :=
      len2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm _ _ i]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := k.val + 5 - m + i) (by omega)
      have hy := val_cases4m (m := m)
        (a := m + 2 + 3 * i) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead,
        cpt_add_u2 hm _ _ (m / 3 - 1)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he h3 2 k, sigNat_two, hsig,
        sp2_row hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hD7b : k.val + 4 = 2 * (m / 3) + m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k = (cpt (k.val + 5 - m) (m + 2) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [hs, sp2_row hm4 (by omega) (by omega)]
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 3 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = k.val + m / 3 + 1 :=
      sig2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have hlen : len2 m k.val = m / 3 :=
      len2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm _ _ i]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := k.val + 5 - m + i) (by omega)
      have hy := val_cases4m (m := m)
        (a := m + 2 + 3 * i) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead,
        cpt_add_u2 hm _ _ (m / 3 - 1)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he h3 2 k, sigNat_two, hsig,
        sp2_rowZero hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hD7c : k.val + 3 = 2 * (m / 3) + m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k = (cpt (k.val + 5 - m) (m + 2) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [hs, sp2_row hm4 (by omega) (by omega)]
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 3 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = k.val + m / 3 + 1 :=
      sig2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have hlen : len2 m k.val = m / 3 :=
      len2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm _ _ i]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := k.val + 5 - m + i) (by omega)
      have hy := val_cases4m (m := m)
        (a := m + 2 + 3 * i) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead,
        cpt_add_u2 hm _ _ (m / 3 - 1)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he h3 2 k, sigNat_two, hsig,
        sp2_preLast hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hD8 : k.val + 2 = 2 * (m / 3) + m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k = (cpt (k.val + 5 - m) (m + 2) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [hs, sp2_row hm4 (by omega) (by omega)]
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 3 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = m + m / 3 - 1 :=
      sig2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))
    have hlen : len2 m k.val = 2 * (m / 3) :=
      len2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm _ _ i]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := k.val + 5 - m + i) (by omega)
      have hy := val_cases4m (m := m)
        (a := m + 2 + 3 * i) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead,
        cpt_add_u2 hm _ _ (2 * (m / 3) - 1)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he h3 2 k, sigNat_two, hsig,
        sp2_row hm4 (by omega) (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hD9a : k.val + 5 ≤ 2 * m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k = (cpt (k.val + 5 - m) (m + 2) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [hs, sp2_row hm4 (by omega) (by omega)]
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 3 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = 6 * m - 7 - 3 * k.val :=
      sig2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have hlen : len2 m k.val = 2 * m - 2 - k.val :=
      len2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm _ _ i]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := k.val + 5 - m + i) (by omega)
      have hy := val_cases4m (m := m)
        (a := m + 2 + 3 * i) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead,
        cpt_add_u2 hm _ _ (2 * m - 2 - k.val - 1)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he h3 2 k, sigNat_two, hsig,
        sp2_col hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hD9b : k.val + 4 = 2 * m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k = (cpt (1) (m + 2) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [hs, sp2_rowZero hm4 (by omega)]
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 3 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = 6 * m - 7 - 3 * k.val :=
      sig2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have hlen : len2 m k.val = 2 * m - 2 - k.val :=
      len2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm _ _ i]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 1 + i) (by omega)
      have hy := val_cases4m (m := m)
        (a := m + 2 + 3 * i) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead,
        cpt_add_u2 hm _ _ (2 * m - 2 - k.val - 1)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he h3 2 k, sigNat_two, hsig,
        sp2_col hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hD9c : k.val + 3 = 2 * m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k = (cpt (2) (m + 2) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [hs, sp2_preLast hm4 (by omega)]
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 3 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = 6 * m - 7 - 3 * k.val :=
      sig2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have hlen : len2 m k.val = 2 * m - 2 - k.val :=
      len2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm _ _ i]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 2 + i) (by omega)
      have hy := val_cases4m (m := m)
        (a := m + 2 + 3 * i) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead,
        cpt_add_u2 hm _ _ (2 * m - 2 - k.val - 1)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he h3 2 k, sigNat_two, hsig,
        sp2_col hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  by_cases hD10 : k.val + 2 = 2 * m
  · have hs : (seamSucc m k).val = k.val + 1 :=
      seamSucc_val_of_lt (by omega)
    have hhead : headF 2 m k = (cpt (2) (3) : TerminalQ m) := by
      show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
      rw [hs, sp2_last hm4 (by omega)]
      rw [show (uVec m 2 : TerminalQ m) = cpt 1 3 from rfl,
        cpt_add]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
    have hsig : sig2 m k.val = 3 :=
      sig2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))))
    have hlen : len2 m k.val = 1 :=
      len2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))))
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [lenNat_two, hlen] at hi
      rw [hhead, cpt_add_u2 hm _ _ i]
      intro hact
      have hval := active2_cpt hm4 hact
      have hx := val_cases4m (m := m)
        (a := 2 + i) (by omega)
      have hy := val_cases4m (m := m)
        (a := 3 + 3 * i) (by omega)
      omega
    · rw [lenNat_two, hlen, hhead,
        cpt_add_u2 hm _ _ (1 - 1)]
      show _ = seamPoint2Nat m (sigF 2 m k).val
      rw [sigF_val hm he h3 2 k, sigNat_two, hsig,
        sp2_col hm4 (by omega)]
      all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  have hs : (seamSucc m k).val = 0 :=
    seamSucc_val_last (by omega)
  have hhead : headF 2 m k = (cpt (3) (3) : TerminalQ m) := by
    show seamPoint2Nat m (seamSucc m k).val + uVec m 2 = _
    rw [hs, sp2_col hm4 (by omega)]
    rw [show (uVec m 2 : TerminalQ m) = cpt 1 3 from rfl,
      cpt_add]
    all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))
  have hsig : sig2 m k.val = 0 :=
    sig2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))))))))
  have hlen : len2 m k.val = m :=
    len2_eq hm he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))))))))
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [lenNat_two, hlen] at hi
    rw [hhead, cpt_add_u2 hm _ _ i]
    intro hact
    have hval := active2_cpt hm4 hact
    have hx := val_cases4m (m := m)
      (a := 3 + i) (by omega)
    have hy := val_cases4m (m := m)
      (a := 3 + 3 * i) (by omega)
    omega
  · rw [lenNat_two, hlen, hhead,
      cpt_add_u2 hm _ _ (m - 1)]
    show _ = seamPoint2Nat m (sigF 2 m k).val
    rw [sigF_val hm he h3 2 k, sigNat_two, hsig,
      sp2_col hm4 (by omega)]
    all_goals exact cpt_congr (castMod (by omega)) (castMod (by omega))

end Specs

/-! ## Level 2: the label successor is a single `2m`-cycle

`σ_c` is spliced along the `(m/3 − 1)`-element transversal `ι_c` (the low
labels with `d−4` and `d−1` skipped, shifted by the per-color offset
`0 / 3 / m`), with interval lengths `(6, …, 6, 11, 7, 7, 6, 5)`: the first
return of `σ_c` to the transversal is exactly `+2` on `ZMod (m/3 − 1)`,
and `+2` generates `ZMod (m/3 − 1)` exactly because `m` is even. -/

section LevelTwo

/-- Level-2 transversal core: the strictly increasing enumeration of
`[0, d] \ {d−4, d−1}` (`d = m/3`), shifted by the color offset. -/
def iotaNat (c : Fin 3) (m s : Nat) : Nat :=
  if c = 0 then
    (if s + 5 ≤ m / 3 then s else if s + 3 ≤ m / 3 then s + 1 else s + 2)
  else if c = 1 then
    3 + (if s + 5 ≤ m / 3 then s else if s + 3 ≤ m / 3 then s + 1
      else s + 2)
  else
    m + (if s + 5 ≤ m / 3 then s else if s + 3 ≤ m / 3 then s + 1
      else s + 2)

/-- Level-2 transversal: `m/3 − 1` interval heads on the label circle. -/
def iota (c : Fin 3) (m : Nat) [NeZero (m / 3 - 1)] (t : ZMod (m / 3 - 1)) :
    Fin (2 * m) :=
  ⟨iotaNat c m t.val % (2 * m), Nat.mod_lt _ (by
    have h1 : 0 < m / 3 - 1 := Nat.pos_of_ne_zero (NeZero.ne _)
    omega)⟩

private theorem iotaNat_zero (m s : Nat) :
    iotaNat 0 m s
      = (if s + 5 ≤ m / 3 then s else if s + 3 ≤ m / 3 then s + 1
          else s + 2) := rfl

private theorem iotaNat_one (m s : Nat) :
    iotaNat 1 m s
      = 3 + (if s + 5 ≤ m / 3 then s else if s + 3 ≤ m / 3 then s + 1
          else s + 2) := rfl

private theorem iotaNat_two (m s : Nat) :
    iotaNat 2 m s
      = m + (if s + 5 ≤ m / 3 then s else if s + 3 ≤ m / 3 then s + 1
          else s + 2) := rfl

private theorem iota0_eq {m s v : Nat} (hm : 18 ≤ m)
    (h : (s + 5 ≤ m / 3 ∧ v = s) ∨
      (s + 3 ≤ m / 3 ∧ m / 3 ≤ s + 4 ∧ v = s + 1) ∨
      (m / 3 ≤ s + 2 ∧ v = s + 2)) :
    iotaNat 0 m s = v := by
  rw [iotaNat_zero]
  split_ifs <;> omega

private theorem iota1_eq {m s v : Nat} (hm : 18 ≤ m)
    (h : (s + 5 ≤ m / 3 ∧ v = s + 3) ∨
      (s + 3 ≤ m / 3 ∧ m / 3 ≤ s + 4 ∧ v = s + 4) ∨
      (m / 3 ≤ s + 2 ∧ v = s + 5)) :
    iotaNat 1 m s = v := by
  rw [iotaNat_one]
  split_ifs <;> omega

private theorem iota2_eq {m s v : Nat} (hm : 18 ≤ m)
    (h : (s + 5 ≤ m / 3 ∧ v = m + s) ∨
      (s + 3 ≤ m / 3 ∧ m / 3 ≤ s + 4 ∧ v = m + s + 1) ∨
      (m / 3 ≤ s + 2 ∧ v = m + s + 2)) :
    iotaNat 2 m s = v := by
  rw [iotaNat_two]
  split_ifs <;> omega

private theorem iota_val {m : Nat} [NeZero (m / 3 - 1)] (hm : 18 ≤ m)
    {c : Fin 3} {t : ZMod (m / 3 - 1)} :
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

/-- The level-2 interval lengths along the transversal. -/
def lenL (m s : Nat) : Nat :=
  if s + 6 = m / 3 then 11
  else if s + 5 = m / 3 then 7
  else if s + 4 = m / 3 then 7
  else if s + 3 = m / 3 then 6
  else if s + 2 = m / 3 then 5
  else 6

private theorem lenL_eq {m s v : Nat} (hm : 18 ≤ m)
    (h : (s + 6 = m / 3 ∧ v = 11) ∨ (s + 5 = m / 3 ∧ v = 7) ∨
      (s + 4 = m / 3 ∧ v = 7) ∨ (s + 3 = m / 3 ∧ v = 6) ∨
      (s + 2 = m / 3 ∧ v = 5) ∨ (s + 7 ≤ m / 3 ∧ v = 6)) :
    lenL m s = v := by
  unfold lenL
  split_ifs <;> omega

private theorem lenL_pos {m : Nat} (hm : 18 ≤ m) (s : Nat) :
    0 < lenL m s := by
  unfold lenL
  split_ifs <;> omega

/-- Value of the transversal index after the `+2` step. -/
private theorem val_add2 {m : Nat} [NeZero (m / 3 - 1)] (hm : 18 ≤ m)
    (t : ZMod (m / 3 - 1)) :
    ((t + 2).val = t.val + 2 ∧ t.val + 2 < m / 3 - 1) ∨
      ((t + 2).val = t.val + 2 - (m / 3 - 1) ∧
        m / 3 - 1 ≤ t.val + 2) := by
  have hts := ZMod.val_lt t
  have hcast : t + 2 = ((t.val + 2 : Nat) : ZMod (m / 3 - 1)) := by
    rw [show ((t.val + 2 : Nat) : ZMod (m / 3 - 1))
        = ((t.val : Nat) : ZMod (m / 3 - 1)) + 2 by push_cast; ring,
      ZMod.natCast_zmod_val]
  rcases Nat.lt_or_ge (t.val + 2) (m / 3 - 1) with hlt | hge
  · exact Or.inl ⟨by rw [hcast]; exact ZMod.val_natCast_of_lt hlt, hlt⟩
  · refine Or.inr ⟨?_, hge⟩
    rw [hcast, ZMod.val_natCast, Nat.mod_eq_sub_mod hge,
      Nat.mod_eq_of_lt (by omega)]

private theorem addTwo_iterate {n : Nat} [NeZero n] (x : ZMod n) :
    ∀ j : Nat, (fun z : ZMod n => z + 2)^[j] x = x + (j : Nat) * 2
  | 0 => by
      rw [Function.iterate_zero_apply, Nat.cast_zero, zero_mul, add_zero]
  | j + 1 => by
      rw [Function.iterate_succ_apply', addTwo_iterate x j]
      show x + (j : Nat) * 2 + 2 = _
      push_cast
      ring

/-- `+2` is a single cycle on `ZMod n` when `gcd(2, n) = 1` — the source of
the evenness hypothesis (`n = m/3 − 1` is odd because `m/3` is even). -/
private theorem addTwo_singleCycle (n : Nat) [NeZero n]
    (hcop : Nat.Coprime 2 n) :
    IsSingleCycleMap (fun z : ZMod n => z + 2) := by
  refine ⟨(Equiv.addRight (2 : ZMod n)).bijective, ?_⟩
  intro x y
  refine ⟨((y - x) * (((ZMod.unitOfCoprime 2 hcop)⁻¹ : (ZMod n)ˣ) :
    ZMod n)).val, ?_⟩
  rw [addTwo_iterate, ZMod.natCast_zmod_val]
  have hcoe : ((ZMod.unitOfCoprime 2 hcop : (ZMod n)ˣ) : ZMod n) = 2 := by
    rw [ZMod.coe_unitOfCoprime]
    push_cast
    ring
  have hinv : (((ZMod.unitOfCoprime 2 hcop)⁻¹ : (ZMod n)ˣ) : ZMod n) * 2
      = 1 := by
    rw [← hcoe, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc x + (y - x) * (((ZMod.unitOfCoprime 2 hcop)⁻¹ : (ZMod n)ˣ) :
        ZMod n) * 2
      = x + (y - x) * ((((ZMod.unitOfCoprime 2 hcop)⁻¹ : (ZMod n)ˣ) :
          ZMod n) * 2) := by ring
    _ = y := by rw [hinv]; ring

end LevelTwo


set_option maxHeartbeats 3200000 in
private theorem chain0 {m : Nat} [NeZero m] [NeZero (m / 3 - 1)]
    (hm : 18 ≤ m) (he : m % 2 = 0) (h3 : m % 3 = 0)
    (t : ZMod (m / 3 - 1)) :
    (sigF 0 m)^[lenL m t.val] (iota 0 m t)
      = iota 0 m (t + 2) := by
  have hd1 : 0 < m / 3 - 1 := Nat.pos_of_ne_zero (NeZero.ne _)
  have hts := ZMod.val_lt t
  have ht2 := val_add2 hm t
  have hm12 : 12 ≤ m := by omega
  by_cases hG : t.val + 7 ≤ m / 3
  · have hlen : lenL m t.val = 6 := lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))
    rw [hlen]
    have v0 : (iota 0 m t).val = t.val := by
      rw [iota_val hm]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m t)).val = (m / 3) + t.val + 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m t))).val = 2 * (m / 3) + t.val + 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))).val = 2 * m - 3 * t.val - 13 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t))))).val = 2 * m - 3 * t.val - 12 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v5 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))))).val = 2 * m - 3 * t.val - 11 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v4]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v6 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t))))))).val = t.val + 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v5]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))
    have hiter : (sigF 0 m)^[6] (iota 0 m t)
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))))) := rfl
    refine Fin.ext ?_
    rw [hiter, v6, iota_val hm]
    symm
    exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
  by_cases hS6 : t.val + 6 = m / 3
  · have hlen : lenL m t.val = 11 := lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    rw [hlen]
    have v0 : (iota 0 m t).val = (m / 3) - 6 := by
      rw [iota_val hm]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m t)).val = 2 * (m / 3) - 5 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m t))).val = m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))).val = m + 5 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t))))).val = m + 6 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v5 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))))).val = m + 7 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v4]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v6 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t))))))).val = (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v5]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))
    have v7 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))))))).val = 2 * (m / 3) - 3 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v6]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v8 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t))))))))).val = m - 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v7]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v9 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))))))))).val = m + 3 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v8]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    have v10 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t))))))))))).val = m + 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v9]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v11 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))))))))))).val = (m / 3) - 3 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v10]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))
    have hiter : (sigF 0 m)^[11] (iota 0 m t)
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t))))))))))) := rfl
    refine Fin.ext ?_
    rw [hiter, v11, iota_val hm]
    symm
    exact iota0_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
  by_cases hS5 : t.val + 5 = m / 3
  · have hlen : lenL m t.val = 7 := lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    rw [hlen]
    have v0 : (iota 0 m t).val = (m / 3) - 5 := by
      rw [iota_val hm]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m t)).val = 2 * (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m t))).val = m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))).val = m + 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t))))).val = m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))
    have v5 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))))).val = m := by
      rw [sigF_val hm12 he h3, sigNat_zero, v4]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    have v6 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t))))))).val = m + 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v5]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))
    have v7 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))))))).val = (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v6]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))
    have hiter : (sigF 0 m)^[7] (iota 0 m t)
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t))))))) := rfl
    refine Fin.ext ?_
    rw [hiter, v7, iota_val hm]
    symm
    exact iota0_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
  by_cases hS4 : t.val + 4 = m / 3
  · have hlen : lenL m t.val = 7 := lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    rw [hlen]
    have v0 : (iota 0 m t).val = (m / 3) - 3 := by
      rw [iota_val hm]
      exact iota0_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 0 m (iota 0 m t)).val = 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m t))).val = (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))).val = 2 * (m / 3) := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t))))).val = 2 * m - 7 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v5 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))))).val = 2 * m - 6 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v4]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v6 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t))))))).val = 2 * m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v5]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))
    have v7 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))))))).val = (m / 3) := by
      rw [sigF_val hm12 he h3, sigNat_zero, v6]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))))
    have hiter : (sigF 0 m)^[7] (iota 0 m t)
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t))))))) := rfl
    refine Fin.ext ?_
    rw [hiter, v7, iota_val hm]
    symm
    exact iota0_eq hm (Or.inr (Or.inr (⟨by omega, by omega⟩)))
  by_cases hS3 : t.val + 3 = m / 3
  · have hlen : lenL m t.val = 6 := lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    rw [hlen]
    have v0 : (iota 0 m t).val = (m / 3) - 2 := by
      rw [iota_val hm]
      exact iota0_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 0 m (iota 0 m t)).val = 2 * (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m t))).val = 2 * m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))).val = 2 * m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t))))).val = 2 * m - 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v5 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))))).val = 2 * m - 5 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v4]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))
    have v6 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t))))))).val = 0 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v5]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))
    have hiter : (sigF 0 m)^[6] (iota 0 m t)
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))))) := rfl
    refine Fin.ext ?_
    rw [hiter, v6, iota_val hm]
    symm
    exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
  have hlen : lenL m t.val = 5 := lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
  rw [hlen]
  have v0 : (iota 0 m t).val = (m / 3) := by
    rw [iota_val hm]
    exact iota0_eq hm (Or.inr (Or.inr (⟨by omega, by omega⟩)))
  have v1 : (sigF 0 m (iota 0 m t)).val = 2 * (m / 3) + 1 := by
    rw [sigF_val hm12 he h3, sigNat_zero, v0]
    exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
  have v2 : (sigF 0 m (sigF 0 m (iota 0 m t))).val = 2 * m - 10 := by
    rw [sigF_val hm12 he h3, sigNat_zero, v1]
    exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
  have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))).val = 2 * m - 9 := by
    rw [sigF_val hm12 he h3, sigNat_zero, v2]
    exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
  have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t))))).val = 2 * m - 8 := by
    rw [sigF_val hm12 he h3, sigNat_zero, v3]
    exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
  have v5 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t)))))).val = 1 := by
    rw [sigF_val hm12 he h3, sigNat_zero, v4]
    exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))
  have hiter : (sigF 0 m)^[5] (iota 0 m t)
      = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m t))))) := rfl
  refine Fin.ext ?_
  rw [hiter, v5, iota_val hm]
  symm
  exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))

set_option maxHeartbeats 3200000 in
private theorem chain1 {m : Nat} [NeZero m] [NeZero (m / 3 - 1)]
    (hm : 18 ≤ m) (he : m % 2 = 0) (h3 : m % 3 = 0)
    (t : ZMod (m / 3 - 1)) :
    (sigF 1 m)^[lenL m t.val] (iota 1 m t)
      = iota 1 m (t + 2) := by
  have hd1 : 0 < m / 3 - 1 := Nat.pos_of_ne_zero (NeZero.ne _)
  have hts := ZMod.val_lt t
  have ht2 := val_add2 hm t
  have hm12 : 12 ≤ m := by omega
  by_cases hG : t.val + 7 ≤ m / 3
  · have hlen : lenL m t.val = 6 := lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))
    rw [hlen]
    have v0 : (iota 1 m t).val = t.val + 3 := by
      rw [iota_val hm]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m t)).val = (m / 3) + t.val + 4 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m t))).val = 2 * (m / 3) + t.val + 5 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))).val = 2 * m - 3 * t.val - 10 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))).val = 2 * m - 3 * t.val - 9 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have v5 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))))).val = 2 * m - 3 * t.val - 8 := by
      rw [sigF_val hm12 he h3, sigNat_one, v4]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have v6 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))))).val = t.val + 5 := by
      rw [sigF_val hm12 he h3, sigNat_one, v5]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))))
    have hiter : (sigF 1 m)^[6] (iota 1 m t)
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))))) := rfl
    refine Fin.ext ?_
    rw [hiter, v6, iota_val hm]
    symm
    exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
  by_cases hS6 : t.val + 6 = m / 3
  · have hlen : lenL m t.val = 11 := lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    rw [hlen]
    have v0 : (iota 1 m t).val = (m / 3) - 3 := by
      rw [iota_val hm]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m t)).val = 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m t))).val = m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))).val = m + 8 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))).val = m + 9 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have v5 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))))).val = m + 10 := by
      rw [sigF_val hm12 he h3, sigNat_one, v4]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have v6 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))))).val = (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v5]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))))
    have v7 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))))))).val = 2 * (m / 3) := by
      rw [sigF_val hm12 he h3, sigNat_one, v6]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v8 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))))))).val = m + 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v7]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v9 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))))))))).val = m + 6 := by
      rw [sigF_val hm12 he h3, sigNat_one, v8]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))
    have v10 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))))))))).val = m + 7 := by
      rw [sigF_val hm12 he h3, sigNat_one, v9]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have v11 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))))))))))).val = (m / 3) := by
      rw [sigF_val hm12 he h3, sigNat_one, v10]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))))
    have hiter : (sigF 1 m)^[11] (iota 1 m t)
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))))))))) := rfl
    refine Fin.ext ?_
    rw [hiter, v11, iota_val hm]
    symm
    exact iota1_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
  by_cases hS5 : t.val + 5 = m / 3
  · have hlen : lenL m t.val = 7 := lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    rw [hlen]
    have v0 : (iota 1 m t).val = (m / 3) - 2 := by
      rw [iota_val hm]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m t)).val = 2 * (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m t))).val = m := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))).val = m + 5 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))).val = m + 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))))
    have v5 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))))).val = m + 3 := by
      rw [sigF_val hm12 he h3, sigNat_one, v4]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))
    have v6 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))))).val = m + 4 := by
      rw [sigF_val hm12 he h3, sigNat_one, v5]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))
    have v7 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))))))).val = (m / 3) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v6]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))))
    have hiter : (sigF 1 m)^[7] (iota 1 m t)
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))))) := rfl
    refine Fin.ext ?_
    rw [hiter, v7, iota_val hm]
    symm
    exact iota1_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
  by_cases hS4 : t.val + 4 = m / 3
  · have hlen : lenL m t.val = 7 := lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    rw [hlen]
    have v0 : (iota 1 m t).val = (m / 3) := by
      rw [iota_val hm]
      exact iota1_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 1 m (iota 1 m t)).val = 2 * (m / 3) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m t))).val = (m / 3) + 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))).val = 2 * (m / 3) + 3 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))).val = 2 * m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v5 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))))).val = 2 * m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_one, v4]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have v6 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))))).val = 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v5]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))))
    have v7 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))))))).val = (m / 3) + 3 := by
      rw [sigF_val hm12 he h3, sigNat_one, v6]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    have hiter : (sigF 1 m)^[7] (iota 1 m t)
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))))) := rfl
    refine Fin.ext ?_
    rw [hiter, v7, iota_val hm]
    symm
    exact iota1_eq hm (Or.inr (Or.inr (⟨by omega, by omega⟩)))
  by_cases hS3 : t.val + 3 = m / 3
  · have hlen : lenL m t.val = 6 := lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    rw [hlen]
    have v0 : (iota 1 m t).val = (m / 3) + 1 := by
      rw [iota_val hm]
      exact iota1_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 1 m (iota 1 m t)).val = 2 * (m / 3) + 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m t))).val = 2 * m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))).val = 0 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))).val = 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v5 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))))).val = 2 * m - 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v4]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    have v6 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))))).val = 3 := by
      rw [sigF_val hm12 he h3, sigNat_one, v5]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))))
    have hiter : (sigF 1 m)^[6] (iota 1 m t)
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))))) := rfl
    refine Fin.ext ?_
    rw [hiter, v6, iota_val hm]
    symm
    exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
  have hlen : lenL m t.val = 5 := lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
  rw [hlen]
  have v0 : (iota 1 m t).val = (m / 3) + 3 := by
    rw [iota_val hm]
    exact iota1_eq hm (Or.inr (Or.inr (⟨by omega, by omega⟩)))
  have v1 : (sigF 1 m (iota 1 m t)).val = 2 * (m / 3) + 4 := by
    rw [sigF_val hm12 he h3, sigNat_one, v0]
    exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
  have v2 : (sigF 1 m (sigF 1 m (iota 1 m t))).val = 2 * m - 7 := by
    rw [sigF_val hm12 he h3, sigNat_one, v1]
    exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
  have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))).val = 2 * m - 6 := by
    rw [sigF_val hm12 he h3, sigNat_one, v2]
    exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
  have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))).val = 2 * m - 5 := by
    rw [sigF_val hm12 he h3, sigNat_one, v3]
    exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
  have v5 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t)))))).val = 4 := by
    rw [sigF_val hm12 he h3, sigNat_one, v4]
    exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))))
  have hiter : (sigF 1 m)^[5] (iota 1 m t)
      = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m t))))) := rfl
  refine Fin.ext ?_
  rw [hiter, v5, iota_val hm]
  symm
  exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))

set_option maxHeartbeats 3200000 in
private theorem chain2 {m : Nat} [NeZero m] [NeZero (m / 3 - 1)]
    (hm : 18 ≤ m) (he : m % 2 = 0) (h3 : m % 3 = 0)
    (t : ZMod (m / 3 - 1)) :
    (sigF 2 m)^[lenL m t.val] (iota 2 m t)
      = iota 2 m (t + 2) := by
  have hd1 : 0 < m / 3 - 1 := Nat.pos_of_ne_zero (NeZero.ne _)
  have hts := ZMod.val_lt t
  have ht2 := val_add2 hm t
  have hm12 : 12 ≤ m := by omega
  by_cases hG : t.val + 7 ≤ m / 3
  · have hlen : lenL m t.val = 6 := lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))
    rw [hlen]
    have v0 : (iota 2 m t).val = m + t.val := by
      rw [iota_val hm]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m t)).val = m + (m / 3) + t.val + 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m t))).val = m + 2 * (m / 3) + t.val + 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))).val = m - 3 * t.val - 13 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))).val = m - 3 * t.val - 12 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v5 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))))).val = m - 3 * t.val - 11 := by
      rw [sigF_val hm12 he h3, sigNat_two, v4]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v6 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))))).val = m + t.val + 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v5]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩)))))))
    have hiter : (sigF 2 m)^[6] (iota 2 m t)
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))))) := rfl
    refine Fin.ext ?_
    rw [hiter, v6, iota_val hm]
    symm
    exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
  by_cases hS6 : t.val + 6 = m / 3
  · have hlen : lenL m t.val = 11 := lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    rw [hlen]
    have v0 : (iota 2 m t).val = m + (m / 3) - 6 := by
      rw [iota_val hm]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m t)).val = m + 2 * (m / 3) - 5 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m t))).val = 2 * m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))).val = 5 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))).val = 6 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v5 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))))).val = 7 := by
      rw [sigF_val hm12 he h3, sigNat_two, v4]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v6 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))))).val = m + (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v5]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩)))))))
    have v7 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))))))).val = m + 2 * (m / 3) - 3 := by
      rw [sigF_val hm12 he h3, sigNat_two, v6]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v8 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))))))).val = 2 * m - 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v7]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v9 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))))))))).val = 3 := by
      rw [sigF_val hm12 he h3, sigNat_two, v8]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))))
    have v10 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))))))))).val = 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v9]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v11 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))))))))))).val = m + (m / 3) - 3 := by
      rw [sigF_val hm12 he h3, sigNat_two, v10]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩)))))))
    have hiter : (sigF 2 m)^[11] (iota 2 m t)
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))))))))) := rfl
    refine Fin.ext ?_
    rw [hiter, v11, iota_val hm]
    symm
    exact iota2_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
  by_cases hS5 : t.val + 5 = m / 3
  · have hlen : lenL m t.val = 7 := lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    rw [hlen]
    have v0 : (iota 2 m t).val = m + (m / 3) - 5 := by
      rw [iota_val hm]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m t)).val = m + 2 * (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m t))).val = 2 * m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))).val = 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))).val = 2 * m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    have v5 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))))).val = 0 := by
      rw [sigF_val hm12 he h3, sigNat_two, v4]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))))))))
    have v6 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))))).val = 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v5]
      exact sig2_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v7 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))))))).val = m + (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v6]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩)))))))
    have hiter : (sigF 2 m)^[7] (iota 2 m t)
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))))) := rfl
    refine Fin.ext ?_
    rw [hiter, v7, iota_val hm]
    symm
    exact iota2_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
  by_cases hS4 : t.val + 4 = m / 3
  · have hlen : lenL m t.val = 7 := lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    rw [hlen]
    have v0 : (iota 2 m t).val = m + (m / 3) - 3 := by
      rw [iota_val hm]
      exact iota2_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 2 m (iota 2 m t)).val = m + 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m t))).val = m + (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))).val = m + 2 * (m / 3) := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))).val = m - 7 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v5 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))))).val = m - 6 := by
      rw [sigF_val hm12 he h3, sigNat_two, v4]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v6 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))))).val = m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v5]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    have v7 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))))))).val = m + (m / 3) := by
      rw [sigF_val hm12 he h3, sigNat_two, v6]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    have hiter : (sigF 2 m)^[7] (iota 2 m t)
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))))) := rfl
    refine Fin.ext ?_
    rw [hiter, v7, iota_val hm]
    symm
    exact iota2_eq hm (Or.inr (Or.inr (⟨by omega, by omega⟩)))
  by_cases hS3 : t.val + 3 = m / 3
  · have hlen : lenL m t.val = 6 := lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    rw [hlen]
    have v0 : (iota 2 m t).val = m + (m / 3) - 2 := by
      rw [iota_val hm]
      exact iota2_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 2 m (iota 2 m t)).val = m + 2 * (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m t))).val = m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))).val = m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))).val = m - 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v5 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))))).val = m - 5 := by
      rw [sigF_val hm12 he h3, sigNat_two, v4]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    have v6 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))))).val = m := by
      rw [sigF_val hm12 he h3, sigNat_two, v5]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩)))))))
    have hiter : (sigF 2 m)^[6] (iota 2 m t)
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))))) := rfl
    refine Fin.ext ?_
    rw [hiter, v6, iota_val hm]
    symm
    exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
  have hlen : lenL m t.val = 5 := lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
  rw [hlen]
  have v0 : (iota 2 m t).val = m + (m / 3) := by
    rw [iota_val hm]
    exact iota2_eq hm (Or.inr (Or.inr (⟨by omega, by omega⟩)))
  have v1 : (sigF 2 m (iota 2 m t)).val = m + 2 * (m / 3) + 1 := by
    rw [sigF_val hm12 he h3, sigNat_two, v0]
    exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
  have v2 : (sigF 2 m (sigF 2 m (iota 2 m t))).val = m - 10 := by
    rw [sigF_val hm12 he h3, sigNat_two, v1]
    exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
  have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))).val = m - 9 := by
    rw [sigF_val hm12 he h3, sigNat_two, v2]
    exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
  have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))).val = m - 8 := by
    rw [sigF_val hm12 he h3, sigNat_two, v3]
    exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
  have v5 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t)))))).val = m + 1 := by
    rw [sigF_val hm12 he h3, sigNat_two, v4]
    exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩)))))))
  have hiter : (sigF 2 m)^[5] (iota 2 m t)
      = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m t))))) := rfl
  refine Fin.ext ?_
  rw [hiter, v5, iota_val hm]
  symm
  exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))

set_option maxHeartbeats 3200000 in
private theorem cover0 {m : Nat} [NeZero m] [NeZero (m / 3 - 1)]
    (hm : 18 ≤ m) (he : m % 2 = 0) (h3 : m % 3 = 0)
    (k : Fin (2 * m)) :
    ∃ t : ZMod (m / 3 - 1), ∃ j : Nat, j < lenL m t.val ∧
      (sigF 0 m)^[j] (iota 0 m t) = k := by
  have hk := k.isLt
  have hd1 : 0 < m / 3 - 1 := Nat.pos_of_ne_zero (NeZero.ne _)
  have hm12 : 12 ≤ m := by omega
  by_cases hc0 : 0 ≤ k.val ∧ k.val + 7 ≤ (m / 3)
  · have hts : ((((k.val : Nat)) : ZMod (m / 3 - 1))).val = k.val :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((k.val : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))
    refine ⟨(((k.val : Nat)) : ZMod (m / 3 - 1)), 0, by omega, ?_⟩
    have v0 : (iota 0 m (((k.val : Nat)) : ZMod (m / 3 - 1))).val = ((k.val)) := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 0 m)^[0] (iota 0 m (((k.val : Nat)) : ZMod (m / 3 - 1)))
        = iota 0 m (((k.val : Nat)) : ZMod (m / 3 - 1)) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hc1 : (m / 3) + 1 ≤ k.val ∧ k.val + 6 ≤ 2 * (m / 3)
  · have hts : ((((k.val - ((m / 3) + 1) : Nat)) : ZMod (m / 3 - 1))).val = k.val - ((m / 3) + 1) :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((k.val - ((m / 3) + 1) : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))
    refine ⟨(((k.val - ((m / 3) + 1) : Nat)) : ZMod (m / 3 - 1)), 1, by omega, ?_⟩
    have v0 : (iota 0 m (((k.val - ((m / 3) + 1) : Nat)) : ZMod (m / 3 - 1))).val = ((k.val - ((m / 3) + 1))) := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m (((k.val - ((m / 3) + 1) : Nat)) : ZMod (m / 3 - 1)))).val = (m / 3) + ((k.val - ((m / 3) + 1))) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 0 m)^[1] (iota 0 m (((k.val - ((m / 3) + 1) : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (iota 0 m (((k.val - ((m / 3) + 1) : Nat)) : ZMod (m / 3 - 1))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hc2 : 2 * (m / 3) + 2 ≤ k.val ∧ k.val + 5 ≤ m
  · have hts : ((((k.val - (2 * (m / 3) + 2) : Nat)) : ZMod (m / 3 - 1))).val = k.val - (2 * (m / 3) + 2) :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((k.val - (2 * (m / 3) + 2) : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))
    refine ⟨(((k.val - (2 * (m / 3) + 2) : Nat)) : ZMod (m / 3 - 1)), 2, by omega, ?_⟩
    have v0 : (iota 0 m (((k.val - (2 * (m / 3) + 2) : Nat)) : ZMod (m / 3 - 1))).val = ((k.val - (2 * (m / 3) + 2))) := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m (((k.val - (2 * (m / 3) + 2) : Nat)) : ZMod (m / 3 - 1)))).val = (m / 3) + ((k.val - (2 * (m / 3) + 2))) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((k.val - (2 * (m / 3) + 2) : Nat)) : ZMod (m / 3 - 1))))).val = 2 * (m / 3) + ((k.val - (2 * (m / 3) + 2))) + 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 0 m)^[2] (iota 0 m (((k.val - (2 * (m / 3) + 2) : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (iota 0 m (((k.val - (2 * (m / 3) + 2) : Nat)) : ZMod (m / 3 - 1)))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hc3 : m + 8 ≤ k.val ∧ k.val + 13 ≤ 2 * m ∧ k.val % 3 = 2
  · have hts : (((((2 * m - 13 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = (2 * m - 13 - k.val) / 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m (((((2 * m - 13 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))
    refine ⟨((((2 * m - 13 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)), 3, by omega, ?_⟩
    have v0 : (iota 0 m ((((2 * m - 13 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = (((2 * m - 13 - k.val) / 3)) := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m ((((2 * m - 13 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))).val = (m / 3) + (((2 * m - 13 - k.val) / 3)) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m ((((2 * m - 13 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * (m / 3) + (((2 * m - 13 - k.val) / 3)) + 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m ((((2 * m - 13 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 * m - 3 * (((2 * m - 13 - k.val) / 3)) - 13 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have hit : (sigF 0 m)^[3] (iota 0 m ((((2 * m - 13 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m ((((2 * m - 13 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hc4 : m + 9 ≤ k.val ∧ k.val + 12 ≤ 2 * m ∧ k.val % 3 = 0
  · have hts : (((((2 * m - 12 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = (2 * m - 12 - k.val) / 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m (((((2 * m - 12 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))
    refine ⟨((((2 * m - 12 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)), 4, by omega, ?_⟩
    have v0 : (iota 0 m ((((2 * m - 12 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = (((2 * m - 12 - k.val) / 3)) := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m ((((2 * m - 12 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))).val = (m / 3) + (((2 * m - 12 - k.val) / 3)) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m ((((2 * m - 12 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * (m / 3) + (((2 * m - 12 - k.val) / 3)) + 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m ((((2 * m - 12 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 * m - 3 * (((2 * m - 12 - k.val) / 3)) - 13 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m ((((2 * m - 12 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))))))).val = 2 * m - 3 * (((2 * m - 12 - k.val) / 3)) - 12 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have hit : (sigF 0 m)^[4] (iota 0 m ((((2 * m - 12 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m ((((2 * m - 12 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v4]
    all_goals omega
  by_cases hc5 : m + 10 ≤ k.val ∧ k.val + 11 ≤ 2 * m ∧ k.val % 3 = 1
  · have hts : (((((2 * m - 11 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = (2 * m - 11 - k.val) / 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m (((((2 * m - 11 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))
    refine ⟨((((2 * m - 11 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)), 5, by omega, ?_⟩
    have v0 : (iota 0 m ((((2 * m - 11 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = (((2 * m - 11 - k.val) / 3)) := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m ((((2 * m - 11 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))).val = (m / 3) + (((2 * m - 11 - k.val) / 3)) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m ((((2 * m - 11 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * (m / 3) + (((2 * m - 11 - k.val) / 3)) + 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m ((((2 * m - 11 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 * m - 3 * (((2 * m - 11 - k.val) / 3)) - 13 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m ((((2 * m - 11 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))))))).val = 2 * m - 3 * (((2 * m - 11 - k.val) / 3)) - 12 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v5 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m ((((2 * m - 11 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))))))).val = 2 * m - 3 * (((2 * m - 11 - k.val) / 3)) - 11 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v4]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have hit : (sigF 0 m)^[5] (iota 0 m ((((2 * m - 11 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m ((((2 * m - 11 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v5]
    all_goals omega
  by_cases hc6 : k.val = (m / 3) - 6
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 0, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 6 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 0 m)^[0] (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hc7 : k.val = 2 * (m / 3) - 5
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 1, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 6 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 5 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 0 m)^[1] (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hc8 : k.val = m - 4
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 2, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 6 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 5 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 0 m)^[2] (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hc9 : k.val = m + 5
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 3, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 6 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 5 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 5 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have hit : (sigF 0 m)^[3] (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hc10 : k.val = m + 6
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 4, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 6 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 5 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 5 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))).val = m + 6 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have hit : (sigF 0 m)^[4] (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v4]
    all_goals omega
  by_cases hc11 : k.val = m + 7
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 5, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 6 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 5 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 5 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))).val = m + 6 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v5 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))).val = m + 7 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v4]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have hit : (sigF 0 m)^[5] (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v5]
    all_goals omega
  by_cases hc12 : k.val = (m / 3) - 4
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 6, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 6 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 5 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 5 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))).val = m + 6 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v5 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))).val = m + 7 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v4]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v6 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))).val = (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v5]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))
    have hit : (sigF 0 m)^[6] (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v6]
    all_goals omega
  by_cases hc13 : k.val = 2 * (m / 3) - 3
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 7, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 6 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 5 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 5 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))).val = m + 6 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v5 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))).val = m + 7 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v4]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v6 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))).val = (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v5]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))
    have v7 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))).val = 2 * (m / 3) - 3 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v6]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 0 m)^[7] (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v7]
    all_goals omega
  by_cases hc14 : k.val = m - 2
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 8, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 6 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 5 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 5 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))).val = m + 6 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v5 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))).val = m + 7 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v4]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v6 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))).val = (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v5]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))
    have v7 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))).val = 2 * (m / 3) - 3 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v6]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v8 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))))).val = m - 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v7]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 0 m)^[8] (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v8]
    all_goals omega
  by_cases hc15 : k.val = m + 3
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 9, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 6 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 5 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 5 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))).val = m + 6 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v5 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))).val = m + 7 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v4]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v6 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))).val = (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v5]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))
    have v7 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))).val = 2 * (m / 3) - 3 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v6]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v8 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))))).val = m - 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v7]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v9 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))))).val = m + 3 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v8]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    have hit : (sigF 0 m)^[9] (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v9]
    all_goals omega
  by_cases hc16 : k.val = m + 4
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 10, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 6 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 5 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 5 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))).val = m + 6 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v5 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))).val = m + 7 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v4]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v6 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))).val = (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v5]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))
    have v7 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))).val = 2 * (m / 3) - 3 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v6]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v8 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))))).val = m - 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v7]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v9 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))))).val = m + 3 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v8]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    have v10 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))))))).val = m + 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v9]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have hit : (sigF 0 m)^[10] (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v10]
    all_goals omega
  by_cases hc17 : k.val = (m / 3) - 5
  · have hts : ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 5 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨(((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)), 0, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 5 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 0 m)^[0] (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))
        = iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hc18 : k.val = 2 * (m / 3) - 4
  · have hts : ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 5 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨(((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)), 1, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 5 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 0 m)^[1] (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hc19 : k.val = m - 3
  · have hts : ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 5 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨(((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)), 2, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 5 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))).val = m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 0 m)^[2] (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hc20 : k.val = m + 2
  · have hts : ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 5 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨(((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)), 3, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 5 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))).val = m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have hit : (sigF 0 m)^[3] (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hc21 : k.val = m - 1
  · have hts : ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 5 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨(((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)), 4, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 5 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))).val = m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))))).val = m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))
    have hit : (sigF 0 m)^[4] (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v4]
    all_goals omega
  by_cases hc22 : k.val = m
  · have hts : ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 5 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨(((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)), 5, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 5 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))).val = m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))))).val = m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))
    have v5 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))))).val = m := by
      rw [sigF_val hm12 he h3, sigNat_zero, v4]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    have hit : (sigF 0 m)^[5] (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v5]
    all_goals omega
  by_cases hc23 : k.val = m + 1
  · have hts : ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 5 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨(((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)), 6, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 5 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))).val = m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))))).val = m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))
    have v5 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))))).val = m := by
      rw [sigF_val hm12 he h3, sigNat_zero, v4]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    have v6 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))))))).val = m + 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v5]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))
    have hit : (sigF 0 m)^[6] (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v6]
    all_goals omega
  by_cases hc24 : k.val = (m / 3) - 3
  · have hts : ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 4 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨(((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)), 0, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have hit : (sigF 0 m)^[0] (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))
        = iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hc25 : k.val = 2 * (m / 3) - 2
  · have hts : ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 4 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨(((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)), 1, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 0 m)^[1] (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hc26 : k.val = (m / 3) - 1
  · have hts : ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 4 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨(((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)), 2, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))).val = (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    have hit : (sigF 0 m)^[2] (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hc27 : k.val = 2 * (m / 3)
  · have hts : ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 4 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨(((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)), 3, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))).val = (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 * (m / 3) := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 0 m)^[3] (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hc28 : k.val = 2 * m - 7
  · have hts : ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 4 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨(((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)), 4, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))).val = (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 * (m / 3) := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))))).val = 2 * m - 7 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have hit : (sigF 0 m)^[4] (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v4]
    all_goals omega
  by_cases hc29 : k.val = 2 * m - 6
  · have hts : ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 4 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨(((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)), 5, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))).val = (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 * (m / 3) := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))))).val = 2 * m - 7 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v5 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))))).val = 2 * m - 6 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v4]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have hit : (sigF 0 m)^[5] (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v5]
    all_goals omega
  by_cases hc30 : k.val = 2 * m - 1
  · have hts : ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 4 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨(((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)), 6, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))).val = (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 * (m / 3) := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))))).val = 2 * m - 7 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v5 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))))).val = 2 * m - 6 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v4]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v6 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))))))).val = 2 * m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v5]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))
    have hit : (sigF 0 m)^[6] (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v6]
    all_goals omega
  by_cases hc31 : k.val = (m / 3) - 2
  · have hts : ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    refine ⟨(((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)), 0, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 2 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have hit : (sigF 0 m)^[0] (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))
        = iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hc32 : k.val = 2 * (m / 3) - 1
  · have hts : ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    refine ⟨(((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)), 1, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 2 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 0 m)^[1] (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hc33 : k.val = 2 * m - 4
  · have hts : ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    refine ⟨(((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)), 2, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 2 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have hit : (sigF 0 m)^[2] (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hc34 : k.val = 2 * m - 3
  · have hts : ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    refine ⟨(((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)), 3, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 2 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 * m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have hit : (sigF 0 m)^[3] (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hc35 : k.val = 2 * m - 2
  · have hts : ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    refine ⟨(((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)), 4, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 2 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 * m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))))).val = 2 * m - 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have hit : (sigF 0 m)^[4] (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v4]
    all_goals omega
  by_cases hc36 : k.val = 2 * m - 5
  · have hts : ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    refine ⟨(((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)), 5, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 2 := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 * m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))))).val = 2 * m - 2 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v5 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))))))).val = 2 * m - 5 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v4]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))
    have hit : (sigF 0 m)^[5] (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v5]
    all_goals omega
  by_cases hc37 : k.val = (m / 3)
  · have hts : ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = 5 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    refine ⟨(((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)), 0, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inr (Or.inr (⟨by omega, by omega⟩)))
    have hit : (sigF 0 m)^[0] (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))
        = iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hc38 : k.val = 2 * (m / 3) + 1
  · have hts : ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = 5 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    refine ⟨(((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)), 1, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inr (Or.inr (⟨by omega, by omega⟩)))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 0 m)^[1] (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hc39 : k.val = 2 * m - 10
  · have hts : ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = 5 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    refine ⟨(((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)), 2, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inr (Or.inr (⟨by omega, by omega⟩)))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 10 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have hit : (sigF 0 m)^[2] (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hc40 : k.val = 2 * m - 9
  · have hts : ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = 5 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    refine ⟨(((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)), 3, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inr (Or.inr (⟨by omega, by omega⟩)))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 10 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 * m - 9 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have hit : (sigF 0 m)^[3] (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hc41 : k.val = 2 * m - 8
  · have hts : ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = 5 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    refine ⟨(((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)), 4, by omega, ?_⟩
    have v0 : (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) := by
      rw [iota_val hm, hts]
      exact iota0_eq hm (Or.inr (Or.inr (⟨by omega, by omega⟩)))
    have v1 : (sigF 0 m (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v0]
      exact sig0_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v2 : (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 10 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v1]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩))))
    have v3 : (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 * m - 9 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v2]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have v4 : (sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))))))).val = 2 * m - 8 := by
      rw [sigF_val hm12 he h3, sigNat_zero, v3]
      exact sig0_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))
    have hit : (sigF 0 m)^[4] (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 0 m (sigF 0 m (sigF 0 m (sigF 0 m (iota 0 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v4]
    all_goals omega
  exfalso
  omega

set_option maxHeartbeats 3200000 in
private theorem cover1 {m : Nat} [NeZero m] [NeZero (m / 3 - 1)]
    (hm : 18 ≤ m) (he : m % 2 = 0) (h3 : m % 3 = 0)
    (k : Fin (2 * m)) :
    ∃ t : ZMod (m / 3 - 1), ∃ j : Nat, j < lenL m t.val ∧
      (sigF 1 m)^[j] (iota 1 m t) = k := by
  have hk := k.isLt
  have hd1 : 0 < m / 3 - 1 := Nat.pos_of_ne_zero (NeZero.ne _)
  have hm12 : 12 ≤ m := by omega
  by_cases hc0 : 3 ≤ k.val ∧ k.val + 4 ≤ (m / 3)
  · have hts : ((((k.val - (3) : Nat)) : ZMod (m / 3 - 1))).val = k.val - (3) :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((k.val - (3) : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))
    refine ⟨(((k.val - (3) : Nat)) : ZMod (m / 3 - 1)), 0, by omega, ?_⟩
    have v0 : (iota 1 m (((k.val - (3) : Nat)) : ZMod (m / 3 - 1))).val = ((k.val - (3))) + 3 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 1 m)^[0] (iota 1 m (((k.val - (3) : Nat)) : ZMod (m / 3 - 1)))
        = iota 1 m (((k.val - (3) : Nat)) : ZMod (m / 3 - 1)) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hc1 : (m / 3) + 4 ≤ k.val ∧ k.val + 3 ≤ 2 * (m / 3)
  · have hts : ((((k.val - ((m / 3) + 4) : Nat)) : ZMod (m / 3 - 1))).val = k.val - ((m / 3) + 4) :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((k.val - ((m / 3) + 4) : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))
    refine ⟨(((k.val - ((m / 3) + 4) : Nat)) : ZMod (m / 3 - 1)), 1, by omega, ?_⟩
    have v0 : (iota 1 m (((k.val - ((m / 3) + 4) : Nat)) : ZMod (m / 3 - 1))).val = ((k.val - ((m / 3) + 4))) + 3 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m (((k.val - ((m / 3) + 4) : Nat)) : ZMod (m / 3 - 1)))).val = (m / 3) + ((k.val - ((m / 3) + 4))) + 4 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have hit : (sigF 1 m)^[1] (iota 1 m (((k.val - ((m / 3) + 4) : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (iota 1 m (((k.val - ((m / 3) + 4) : Nat)) : ZMod (m / 3 - 1))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hc2 : 2 * (m / 3) + 5 ≤ k.val ∧ k.val + 2 ≤ m
  · have hts : ((((k.val - (2 * (m / 3) + 5) : Nat)) : ZMod (m / 3 - 1))).val = k.val - (2 * (m / 3) + 5) :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((k.val - (2 * (m / 3) + 5) : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))
    refine ⟨(((k.val - (2 * (m / 3) + 5) : Nat)) : ZMod (m / 3 - 1)), 2, by omega, ?_⟩
    have v0 : (iota 1 m (((k.val - (2 * (m / 3) + 5) : Nat)) : ZMod (m / 3 - 1))).val = ((k.val - (2 * (m / 3) + 5))) + 3 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m (((k.val - (2 * (m / 3) + 5) : Nat)) : ZMod (m / 3 - 1)))).val = (m / 3) + ((k.val - (2 * (m / 3) + 5))) + 4 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((k.val - (2 * (m / 3) + 5) : Nat)) : ZMod (m / 3 - 1))))).val = 2 * (m / 3) + ((k.val - (2 * (m / 3) + 5))) + 5 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have hit : (sigF 1 m)^[2] (iota 1 m (((k.val - (2 * (m / 3) + 5) : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (iota 1 m (((k.val - (2 * (m / 3) + 5) : Nat)) : ZMod (m / 3 - 1)))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hc3 : m + 11 ≤ k.val ∧ k.val + 10 ≤ 2 * m ∧ k.val % 3 = 2
  · have hts : (((((2 * m - 10 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = (2 * m - 10 - k.val) / 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m (((((2 * m - 10 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))
    refine ⟨((((2 * m - 10 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)), 3, by omega, ?_⟩
    have v0 : (iota 1 m ((((2 * m - 10 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = (((2 * m - 10 - k.val) / 3)) + 3 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m ((((2 * m - 10 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))).val = (m / 3) + (((2 * m - 10 - k.val) / 3)) + 4 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m ((((2 * m - 10 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * (m / 3) + (((2 * m - 10 - k.val) / 3)) + 5 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m ((((2 * m - 10 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 * m - 3 * (((2 * m - 10 - k.val) / 3)) - 10 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have hit : (sigF 1 m)^[3] (iota 1 m ((((2 * m - 10 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m ((((2 * m - 10 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hc4 : m + 12 ≤ k.val ∧ k.val + 9 ≤ 2 * m ∧ k.val % 3 = 0
  · have hts : (((((2 * m - 9 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = (2 * m - 9 - k.val) / 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m (((((2 * m - 9 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))
    refine ⟨((((2 * m - 9 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)), 4, by omega, ?_⟩
    have v0 : (iota 1 m ((((2 * m - 9 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = (((2 * m - 9 - k.val) / 3)) + 3 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m ((((2 * m - 9 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))).val = (m / 3) + (((2 * m - 9 - k.val) / 3)) + 4 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m ((((2 * m - 9 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * (m / 3) + (((2 * m - 9 - k.val) / 3)) + 5 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m ((((2 * m - 9 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 * m - 3 * (((2 * m - 9 - k.val) / 3)) - 10 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m ((((2 * m - 9 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))))))).val = 2 * m - 3 * (((2 * m - 9 - k.val) / 3)) - 9 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have hit : (sigF 1 m)^[4] (iota 1 m ((((2 * m - 9 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m ((((2 * m - 9 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v4]
    all_goals omega
  by_cases hc5 : m + 13 ≤ k.val ∧ k.val + 8 ≤ 2 * m ∧ k.val % 3 = 1
  · have hts : (((((2 * m - 8 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = (2 * m - 8 - k.val) / 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m (((((2 * m - 8 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))
    refine ⟨((((2 * m - 8 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)), 5, by omega, ?_⟩
    have v0 : (iota 1 m ((((2 * m - 8 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = (((2 * m - 8 - k.val) / 3)) + 3 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m ((((2 * m - 8 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))).val = (m / 3) + (((2 * m - 8 - k.val) / 3)) + 4 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m ((((2 * m - 8 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * (m / 3) + (((2 * m - 8 - k.val) / 3)) + 5 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m ((((2 * m - 8 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 * m - 3 * (((2 * m - 8 - k.val) / 3)) - 10 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m ((((2 * m - 8 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))))))).val = 2 * m - 3 * (((2 * m - 8 - k.val) / 3)) - 9 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have v5 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m ((((2 * m - 8 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))))))).val = 2 * m - 3 * (((2 * m - 8 - k.val) / 3)) - 8 := by
      rw [sigF_val hm12 he h3, sigNat_one, v4]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have hit : (sigF 1 m)^[5] (iota 1 m ((((2 * m - 8 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m ((((2 * m - 8 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v5]
    all_goals omega
  by_cases hc6 : k.val = (m / 3) - 3
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 0, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 1 m)^[0] (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hc7 : k.val = 2 * (m / 3) - 2
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 1, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have hit : (sigF 1 m)^[1] (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hc8 : k.val = m - 1
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 2, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have hit : (sigF 1 m)^[2] (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hc9 : k.val = m + 8
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 3, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 8 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have hit : (sigF 1 m)^[3] (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hc10 : k.val = m + 9
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 4, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 8 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))).val = m + 9 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have hit : (sigF 1 m)^[4] (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v4]
    all_goals omega
  by_cases hc11 : k.val = m + 10
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 5, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 8 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))).val = m + 9 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have v5 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))).val = m + 10 := by
      rw [sigF_val hm12 he h3, sigNat_one, v4]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have hit : (sigF 1 m)^[5] (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v5]
    all_goals omega
  by_cases hc12 : k.val = (m / 3) - 1
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 6, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 8 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))).val = m + 9 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have v5 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))).val = m + 10 := by
      rw [sigF_val hm12 he h3, sigNat_one, v4]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have v6 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))).val = (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v5]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))))
    have hit : (sigF 1 m)^[6] (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v6]
    all_goals omega
  by_cases hc13 : k.val = 2 * (m / 3)
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 7, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 8 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))).val = m + 9 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have v5 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))).val = m + 10 := by
      rw [sigF_val hm12 he h3, sigNat_one, v4]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have v6 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))).val = (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v5]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))))
    have v7 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))).val = 2 * (m / 3) := by
      rw [sigF_val hm12 he h3, sigNat_one, v6]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have hit : (sigF 1 m)^[7] (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v7]
    all_goals omega
  by_cases hc14 : k.val = m + 1
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 8, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 8 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))).val = m + 9 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have v5 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))).val = m + 10 := by
      rw [sigF_val hm12 he h3, sigNat_one, v4]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have v6 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))).val = (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v5]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))))
    have v7 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))).val = 2 * (m / 3) := by
      rw [sigF_val hm12 he h3, sigNat_one, v6]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v8 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))))).val = m + 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v7]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have hit : (sigF 1 m)^[8] (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v8]
    all_goals omega
  by_cases hc15 : k.val = m + 6
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 9, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 8 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))).val = m + 9 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have v5 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))).val = m + 10 := by
      rw [sigF_val hm12 he h3, sigNat_one, v4]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have v6 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))).val = (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v5]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))))
    have v7 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))).val = 2 * (m / 3) := by
      rw [sigF_val hm12 he h3, sigNat_one, v6]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v8 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))))).val = m + 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v7]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v9 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))))).val = m + 6 := by
      rw [sigF_val hm12 he h3, sigNat_one, v8]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))
    have hit : (sigF 1 m)^[9] (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v9]
    all_goals omega
  by_cases hc16 : k.val = m + 7
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 10, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 8 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))).val = m + 9 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have v5 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))).val = m + 10 := by
      rw [sigF_val hm12 he h3, sigNat_one, v4]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have v6 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))).val = (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v5]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩))))))))))))))
    have v7 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))).val = 2 * (m / 3) := by
      rw [sigF_val hm12 he h3, sigNat_one, v6]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v8 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))))).val = m + 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v7]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v9 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))))).val = m + 6 := by
      rw [sigF_val hm12 he h3, sigNat_one, v8]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))
    have v10 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))))))).val = m + 7 := by
      rw [sigF_val hm12 he h3, sigNat_one, v9]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have hit : (sigF 1 m)^[10] (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v10]
    all_goals omega
  by_cases hc17 : k.val = (m / 3) - 2
  · have hts : ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 5 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨(((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)), 0, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 2 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 1 m)^[0] (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))
        = iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hc18 : k.val = 2 * (m / 3) - 1
  · have hts : ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 5 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨(((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)), 1, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 2 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have hit : (sigF 1 m)^[1] (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hc19 : k.val = m
  · have hts : ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 5 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨(((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)), 2, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 2 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))).val = m := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have hit : (sigF 1 m)^[2] (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hc20 : k.val = m + 5
  · have hts : ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 5 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨(((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)), 3, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 2 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))).val = m := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 5 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have hit : (sigF 1 m)^[3] (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hc21 : k.val = m + 2
  · have hts : ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 5 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨(((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)), 4, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 2 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))).val = m := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 5 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))))).val = m + 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))))
    have hit : (sigF 1 m)^[4] (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v4]
    all_goals omega
  by_cases hc22 : k.val = m + 3
  · have hts : ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 5 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨(((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)), 5, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 2 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))).val = m := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 5 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))))).val = m + 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))))
    have v5 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))))).val = m + 3 := by
      rw [sigF_val hm12 he h3, sigNat_one, v4]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))
    have hit : (sigF 1 m)^[5] (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v5]
    all_goals omega
  by_cases hc23 : k.val = m + 4
  · have hts : ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 5 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨(((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)), 6, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) - 2 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))).val = m := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 5 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))))).val = m + 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))))
    have v5 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))))).val = m + 3 := by
      rw [sigF_val hm12 he h3, sigNat_one, v4]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))
    have v6 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))))))).val = m + 4 := by
      rw [sigF_val hm12 he h3, sigNat_one, v5]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))
    have hit : (sigF 1 m)^[6] (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v6]
    all_goals omega
  by_cases hc24 : k.val = (m / 3)
  · have hts : ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 4 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨(((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)), 0, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have hit : (sigF 1 m)^[0] (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))
        = iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hc25 : k.val = 2 * (m / 3) + 1
  · have hts : ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 4 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨(((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)), 1, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have hit : (sigF 1 m)^[1] (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hc26 : k.val = (m / 3) + 2
  · have hts : ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 4 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨(((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)), 2, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))).val = (m / 3) + 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    have hit : (sigF 1 m)^[2] (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hc27 : k.val = 2 * (m / 3) + 3
  · have hts : ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 4 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨(((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)), 3, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))).val = (m / 3) + 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 * (m / 3) + 3 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have hit : (sigF 1 m)^[3] (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hc28 : k.val = 2 * m - 4
  · have hts : ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 4 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨(((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)), 4, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))).val = (m / 3) + 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 * (m / 3) + 3 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))))).val = 2 * m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have hit : (sigF 1 m)^[4] (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v4]
    all_goals omega
  by_cases hc29 : k.val = 2 * m - 3
  · have hts : ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 4 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨(((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)), 5, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))).val = (m / 3) + 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 * (m / 3) + 3 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))))).val = 2 * m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v5 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))))).val = 2 * m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_one, v4]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have hit : (sigF 1 m)^[5] (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v5]
    all_goals omega
  by_cases hc30 : k.val = 2
  · have hts : ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 4 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨(((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)), 6, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))).val = (m / 3) + 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 * (m / 3) + 3 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))))).val = 2 * m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v5 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))))).val = 2 * m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_one, v4]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have v6 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))))))).val = 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v5]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))))
    have hit : (sigF 1 m)^[6] (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v6]
    all_goals omega
  by_cases hc31 : k.val = (m / 3) + 1
  · have hts : ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    refine ⟨(((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)), 0, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) + 1 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have hit : (sigF 1 m)^[0] (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))
        = iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hc32 : k.val = 2 * (m / 3) + 2
  · have hts : ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    refine ⟨(((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)), 1, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) + 1 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) + 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have hit : (sigF 1 m)^[1] (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hc33 : k.val = 2 * m - 1
  · have hts : ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    refine ⟨(((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)), 2, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) + 1 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) + 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have hit : (sigF 1 m)^[2] (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hc34 : k.val = 0
  · have hts : ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    refine ⟨(((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)), 3, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) + 1 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) + 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))))).val = 0 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))))))
    have hit : (sigF 1 m)^[3] (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hc35 : k.val = 1
  · have hts : ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    refine ⟨(((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)), 4, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) + 1 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) + 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))))).val = 0 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))))).val = 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 1 m)^[4] (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v4]
    all_goals omega
  by_cases hc36 : k.val = 2 * m - 2
  · have hts : ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    refine ⟨(((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)), 5, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) + 1 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) + 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))))).val = 0 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))))).val = 1 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have v5 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))))))).val = 2 * m - 2 := by
      rw [sigF_val hm12 he h3, sigNat_one, v4]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    have hit : (sigF 1 m)^[5] (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v5]
    all_goals omega
  by_cases hc37 : k.val = (m / 3) + 3
  · have hts : ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = 5 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    refine ⟨(((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)), 0, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) + 3 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inr (Or.inr (⟨by omega, by omega⟩)))
    have hit : (sigF 1 m)^[0] (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))
        = iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hc38 : k.val = 2 * (m / 3) + 4
  · have hts : ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = 5 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    refine ⟨(((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)), 1, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) + 3 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inr (Or.inr (⟨by omega, by omega⟩)))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) + 4 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have hit : (sigF 1 m)^[1] (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hc39 : k.val = 2 * m - 7
  · have hts : ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = 5 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    refine ⟨(((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)), 2, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) + 3 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inr (Or.inr (⟨by omega, by omega⟩)))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) + 4 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 7 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have hit : (sigF 1 m)^[2] (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hc40 : k.val = 2 * m - 6
  · have hts : ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = 5 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    refine ⟨(((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)), 3, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) + 3 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inr (Or.inr (⟨by omega, by omega⟩)))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) + 4 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 7 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 * m - 6 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have hit : (sigF 1 m)^[3] (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hc41 : k.val = 2 * m - 5
  · have hts : ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = 5 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    refine ⟨(((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)), 4, by omega, ?_⟩
    have v0 : (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = (m / 3) + 3 := by
      rw [iota_val hm, hts]
      exact iota1_eq hm (Or.inr (Or.inr (⟨by omega, by omega⟩)))
    have v1 : (sigF 1 m (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))).val = 2 * (m / 3) + 4 := by
      rw [sigF_val hm12 he h3, sigNat_one, v0]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))
    have v2 : (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 7 := by
      rw [sigF_val hm12 he h3, sigNat_one, v1]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))
    have v3 : (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 * m - 6 := by
      rw [sigF_val hm12 he h3, sigNat_one, v2]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have v4 : (sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))))))).val = 2 * m - 5 := by
      rw [sigF_val hm12 he h3, sigNat_one, v3]
      exact sig1_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
    have hit : (sigF 1 m)^[4] (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 1 m (sigF 1 m (sigF 1 m (sigF 1 m (iota 1 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v4]
    all_goals omega
  exfalso
  omega

set_option maxHeartbeats 3200000 in
private theorem cover2 {m : Nat} [NeZero m] [NeZero (m / 3 - 1)]
    (hm : 18 ≤ m) (he : m % 2 = 0) (h3 : m % 3 = 0)
    (k : Fin (2 * m)) :
    ∃ t : ZMod (m / 3 - 1), ∃ j : Nat, j < lenL m t.val ∧
      (sigF 2 m)^[j] (iota 2 m t) = k := by
  have hk := k.isLt
  have hd1 : 0 < m / 3 - 1 := Nat.pos_of_ne_zero (NeZero.ne _)
  have hm12 : 12 ≤ m := by omega
  by_cases hc0 : m ≤ k.val ∧ k.val + 7 ≤ m + (m / 3)
  · have hts : ((((k.val - (m) : Nat)) : ZMod (m / 3 - 1))).val = k.val - (m) :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((k.val - (m) : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))
    refine ⟨(((k.val - (m) : Nat)) : ZMod (m / 3 - 1)), 0, by omega, ?_⟩
    have v0 : (iota 2 m (((k.val - (m) : Nat)) : ZMod (m / 3 - 1))).val = m + ((k.val - (m))) := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 2 m)^[0] (iota 2 m (((k.val - (m) : Nat)) : ZMod (m / 3 - 1)))
        = iota 2 m (((k.val - (m) : Nat)) : ZMod (m / 3 - 1)) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hc1 : m + (m / 3) + 1 ≤ k.val ∧ k.val + 6 ≤ m + 2 * (m / 3)
  · have hts : ((((k.val - (m + (m / 3) + 1) : Nat)) : ZMod (m / 3 - 1))).val = k.val - (m + (m / 3) + 1) :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((k.val - (m + (m / 3) + 1) : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))
    refine ⟨(((k.val - (m + (m / 3) + 1) : Nat)) : ZMod (m / 3 - 1)), 1, by omega, ?_⟩
    have v0 : (iota 2 m (((k.val - (m + (m / 3) + 1) : Nat)) : ZMod (m / 3 - 1))).val = m + ((k.val - (m + (m / 3) + 1))) := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m (((k.val - (m + (m / 3) + 1) : Nat)) : ZMod (m / 3 - 1)))).val = m + (m / 3) + ((k.val - (m + (m / 3) + 1))) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have hit : (sigF 2 m)^[1] (iota 2 m (((k.val - (m + (m / 3) + 1) : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (iota 2 m (((k.val - (m + (m / 3) + 1) : Nat)) : ZMod (m / 3 - 1))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hc2 : m + 2 * (m / 3) + 2 ≤ k.val ∧ k.val + 5 ≤ 2 * m
  · have hts : ((((k.val - (m + 2 * (m / 3) + 2) : Nat)) : ZMod (m / 3 - 1))).val = k.val - (m + 2 * (m / 3) + 2) :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((k.val - (m + 2 * (m / 3) + 2) : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))
    refine ⟨(((k.val - (m + 2 * (m / 3) + 2) : Nat)) : ZMod (m / 3 - 1)), 2, by omega, ?_⟩
    have v0 : (iota 2 m (((k.val - (m + 2 * (m / 3) + 2) : Nat)) : ZMod (m / 3 - 1))).val = m + ((k.val - (m + 2 * (m / 3) + 2))) := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m (((k.val - (m + 2 * (m / 3) + 2) : Nat)) : ZMod (m / 3 - 1)))).val = m + (m / 3) + ((k.val - (m + 2 * (m / 3) + 2))) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((k.val - (m + 2 * (m / 3) + 2) : Nat)) : ZMod (m / 3 - 1))))).val = m + 2 * (m / 3) + ((k.val - (m + 2 * (m / 3) + 2))) + 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have hit : (sigF 2 m)^[2] (iota 2 m (((k.val - (m + 2 * (m / 3) + 2) : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (iota 2 m (((k.val - (m + 2 * (m / 3) + 2) : Nat)) : ZMod (m / 3 - 1)))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hc3 : 8 ≤ k.val ∧ k.val + 13 ≤ m ∧ k.val % 3 = 2
  · have hts : (((((m - 13 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = (m - 13 - k.val) / 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m (((((m - 13 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))
    refine ⟨((((m - 13 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)), 3, by omega, ?_⟩
    have v0 : (iota 2 m ((((m - 13 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = m + (((m - 13 - k.val) / 3)) := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m ((((m - 13 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))).val = m + (m / 3) + (((m - 13 - k.val) / 3)) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m ((((m - 13 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))))).val = m + 2 * (m / 3) + (((m - 13 - k.val) / 3)) + 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m ((((m - 13 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))))).val = m - 3 * (((m - 13 - k.val) / 3)) - 13 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have hit : (sigF 2 m)^[3] (iota 2 m ((((m - 13 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m ((((m - 13 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hc4 : 9 ≤ k.val ∧ k.val + 12 ≤ m ∧ k.val % 3 = 0
  · have hts : (((((m - 12 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = (m - 12 - k.val) / 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m (((((m - 12 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))
    refine ⟨((((m - 12 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)), 4, by omega, ?_⟩
    have v0 : (iota 2 m ((((m - 12 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = m + (((m - 12 - k.val) / 3)) := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m ((((m - 12 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))).val = m + (m / 3) + (((m - 12 - k.val) / 3)) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m ((((m - 12 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))))).val = m + 2 * (m / 3) + (((m - 12 - k.val) / 3)) + 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m ((((m - 12 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))))).val = m - 3 * (((m - 12 - k.val) / 3)) - 13 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m ((((m - 12 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))))))).val = m - 3 * (((m - 12 - k.val) / 3)) - 12 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have hit : (sigF 2 m)^[4] (iota 2 m ((((m - 12 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m ((((m - 12 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v4]
    all_goals omega
  by_cases hc5 : 10 ≤ k.val ∧ k.val + 11 ≤ m ∧ k.val % 3 = 1
  · have hts : (((((m - 11 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = (m - 11 - k.val) / 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m (((((m - 11 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))
    refine ⟨((((m - 11 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)), 5, by omega, ?_⟩
    have v0 : (iota 2 m ((((m - 11 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))).val = m + (((m - 11 - k.val) / 3)) := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m ((((m - 11 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))).val = m + (m / 3) + (((m - 11 - k.val) / 3)) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m ((((m - 11 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))))).val = m + 2 * (m / 3) + (((m - 11 - k.val) / 3)) + 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m ((((m - 11 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))))).val = m - 3 * (((m - 11 - k.val) / 3)) - 13 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m ((((m - 11 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))))))).val = m - 3 * (((m - 11 - k.val) / 3)) - 12 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v5 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m ((((m - 11 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))))))).val = m - 3 * (((m - 11 - k.val) / 3)) - 11 := by
      rw [sigF_val hm12 he h3, sigNat_two, v4]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have hit : (sigF 2 m)^[5] (iota 2 m ((((m - 11 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m ((((m - 11 - k.val) / 3 : Nat)) : ZMod (m / 3 - 1))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v5]
    all_goals omega
  by_cases hc6 : k.val = m + (m / 3) - 6
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 0, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 6 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 2 m)^[0] (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hc7 : k.val = m + 2 * (m / 3) - 5
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 1, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 6 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 5 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have hit : (sigF 2 m)^[1] (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hc8 : k.val = 2 * m - 4
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 2, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 6 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 5 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have hit : (sigF 2 m)^[2] (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hc9 : k.val = 5
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 3, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 6 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 5 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = 5 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have hit : (sigF 2 m)^[3] (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hc10 : k.val = 6
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 4, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 6 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 5 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = 5 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))).val = 6 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have hit : (sigF 2 m)^[4] (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v4]
    all_goals omega
  by_cases hc11 : k.val = 7
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 5, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 6 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 5 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = 5 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))).val = 6 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v5 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))).val = 7 := by
      rw [sigF_val hm12 he h3, sigNat_two, v4]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have hit : (sigF 2 m)^[5] (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v5]
    all_goals omega
  by_cases hc12 : k.val = m + (m / 3) - 4
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 6, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 6 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 5 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = 5 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))).val = 6 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v5 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))).val = 7 := by
      rw [sigF_val hm12 he h3, sigNat_two, v4]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v6 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))).val = m + (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v5]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩)))))))
    have hit : (sigF 2 m)^[6] (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v6]
    all_goals omega
  by_cases hc13 : k.val = m + 2 * (m / 3) - 3
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 7, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 6 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 5 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = 5 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))).val = 6 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v5 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))).val = 7 := by
      rw [sigF_val hm12 he h3, sigNat_two, v4]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v6 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))).val = m + (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v5]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩)))))))
    have v7 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))).val = m + 2 * (m / 3) - 3 := by
      rw [sigF_val hm12 he h3, sigNat_two, v6]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have hit : (sigF 2 m)^[7] (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v7]
    all_goals omega
  by_cases hc14 : k.val = 2 * m - 2
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 8, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 6 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 5 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = 5 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))).val = 6 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v5 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))).val = 7 := by
      rw [sigF_val hm12 he h3, sigNat_two, v4]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v6 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))).val = m + (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v5]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩)))))))
    have v7 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))).val = m + 2 * (m / 3) - 3 := by
      rw [sigF_val hm12 he h3, sigNat_two, v6]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v8 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))))).val = 2 * m - 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v7]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have hit : (sigF 2 m)^[8] (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v8]
    all_goals omega
  by_cases hc15 : k.val = 3
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 9, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 6 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 5 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = 5 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))).val = 6 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v5 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))).val = 7 := by
      rw [sigF_val hm12 he h3, sigNat_two, v4]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v6 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))).val = m + (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v5]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩)))))))
    have v7 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))).val = m + 2 * (m / 3) - 3 := by
      rw [sigF_val hm12 he h3, sigNat_two, v6]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v8 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))))).val = 2 * m - 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v7]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v9 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))))).val = 3 := by
      rw [sigF_val hm12 he h3, sigNat_two, v8]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))))
    have hit : (sigF 2 m)^[9] (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v9]
    all_goals omega
  by_cases hc16 : k.val = 4
  · have hts : ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 6 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = 11 := by
      rw [hts]
      exact lenL_eq hm (Or.inl (⟨by omega, by omega⟩))
    refine ⟨(((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)), 10, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 6 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 5 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))).val = 5 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))).val = 6 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v5 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))).val = 7 := by
      rw [sigF_val hm12 he h3, sigNat_two, v4]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v6 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))).val = m + (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v5]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega⟩)))))))
    have v7 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))).val = m + 2 * (m / 3) - 3 := by
      rw [sigF_val hm12 he h3, sigNat_two, v6]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v8 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))))).val = 2 * m - 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v7]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v9 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))))).val = 3 := by
      rw [sigF_val hm12 he h3, sigNat_two, v8]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))))
    have v10 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1))))))))))))).val = 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v9]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have hit : (sigF 2 m)^[10] (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 6 : Nat)) : ZMod (m / 3 - 1)))))))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v10]
    all_goals omega
  by_cases hc17 : k.val = m + (m / 3) - 5
  · have hts : ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 5 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨(((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)), 0, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 5 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 2 m)^[0] (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))
        = iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hc18 : k.val = m + 2 * (m / 3) - 4
  · have hts : ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 5 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨(((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)), 1, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 5 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have hit : (sigF 2 m)^[1] (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hc19 : k.val = 2 * m - 3
  · have hts : ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 5 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨(((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)), 2, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 5 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have hit : (sigF 2 m)^[2] (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hc20 : k.val = 2
  · have hts : ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 5 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨(((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)), 3, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 5 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have hit : (sigF 2 m)^[3] (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hc21 : k.val = 2 * m - 1
  · have hts : ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 5 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨(((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)), 4, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 5 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))))).val = 2 * m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    have hit : (sigF 2 m)^[4] (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v4]
    all_goals omega
  by_cases hc22 : k.val = 0
  · have hts : ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 5 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨(((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)), 5, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 5 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))))).val = 2 * m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    have v5 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))))).val = 0 := by
      rw [sigF_val hm12 he h3, sigNat_two, v4]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))))))))
    have hit : (sigF 2 m)^[5] (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v5]
    all_goals omega
  by_cases hc23 : k.val = 1
  · have hts : ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 5 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    refine ⟨(((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)), 6, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 5 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inl (⟨by omega, by omega⟩))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))).val = 2 * m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))).val = 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))))).val = 2 * m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inl (⟨by omega, by omega⟩)))
    have v5 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))))).val = 0 := by
      rw [sigF_val hm12 he h3, sigNat_two, v4]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩))))))))))))
    have v6 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1))))))))).val = 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v5]
      exact sig2_eq hm12 he h3 (Or.inl (⟨by omega, by omega⟩))
    have hit : (sigF 2 m)^[6] (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 5 : Nat)) : ZMod (m / 3 - 1)))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v6]
    all_goals omega
  by_cases hc24 : k.val = m + (m / 3) - 3
  · have hts : ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 4 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨(((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)), 0, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have hit : (sigF 2 m)^[0] (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))
        = iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hc25 : k.val = m + 2 * (m / 3) - 2
  · have hts : ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 4 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨(((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)), 1, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have hit : (sigF 2 m)^[1] (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hc26 : k.val = m + (m / 3) - 1
  · have hts : ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 4 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨(((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)), 2, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))).val = m + (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))
    have hit : (sigF 2 m)^[2] (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hc27 : k.val = m + 2 * (m / 3)
  · have hts : ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 4 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨(((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)), 3, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))).val = m + (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 2 * (m / 3) := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have hit : (sigF 2 m)^[3] (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hc28 : k.val = m - 7
  · have hts : ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 4 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨(((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)), 4, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))).val = m + (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 2 * (m / 3) := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))))).val = m - 7 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have hit : (sigF 2 m)^[4] (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v4]
    all_goals omega
  by_cases hc29 : k.val = m - 6
  · have hts : ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 4 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨(((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)), 5, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))).val = m + (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 2 * (m / 3) := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))))).val = m - 7 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v5 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))))).val = m - 6 := by
      rw [sigF_val hm12 he h3, sigNat_two, v4]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have hit : (sigF 2 m)^[5] (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v5]
    all_goals omega
  by_cases hc30 : k.val = m - 1
  · have hts : ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 4 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = 7 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    refine ⟨(((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)), 6, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 3 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))).val = m + (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))).val = m + 2 * (m / 3) := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))))).val = m - 7 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v5 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))))).val = m - 6 := by
      rw [sigF_val hm12 he h3, sigNat_two, v4]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v6 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1))))))))).val = m - 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v5]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))
    have hit : (sigF 2 m)^[6] (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 4 : Nat)) : ZMod (m / 3 - 1)))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v6]
    all_goals omega
  by_cases hc31 : k.val = m + (m / 3) - 2
  · have hts : ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    refine ⟨(((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)), 0, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 2 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have hit : (sigF 2 m)^[0] (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))
        = iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hc32 : k.val = m + 2 * (m / 3) - 1
  · have hts : ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    refine ⟨(((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)), 1, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 2 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have hit : (sigF 2 m)^[1] (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hc33 : k.val = m - 4
  · have hts : ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    refine ⟨(((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)), 2, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 2 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))).val = m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have hit : (sigF 2 m)^[2] (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hc34 : k.val = m - 3
  · have hts : ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    refine ⟨(((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)), 3, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 2 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))).val = m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))))).val = m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have hit : (sigF 2 m)^[3] (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hc35 : k.val = m - 2
  · have hts : ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    refine ⟨(((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)), 4, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 2 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))).val = m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))))).val = m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))))).val = m - 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have hit : (sigF 2 m)^[4] (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v4]
    all_goals omega
  by_cases hc36 : k.val = m - 5
  · have hts : ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 3 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = 6 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    refine ⟨(((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)), 5, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) - 2 := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) - 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))).val = m - 4 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))))).val = m - 3 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))))).val = m - 2 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v5 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))))))).val = m - 5 := by
      rw [sigF_val hm12 he h3, sigNat_two, v4]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))
    have hit : (sigF 2 m)^[5] (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 3 : Nat)) : ZMod (m / 3 - 1))))))) := rfl
    refine Fin.ext ?_
    rw [hit, v5]
    all_goals omega
  by_cases hc37 : k.val = m + (m / 3)
  · have hts : ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = 5 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    refine ⟨(((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)), 0, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inr (Or.inr (⟨by omega, by omega⟩)))
    have hit : (sigF 2 m)^[0] (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))
        = iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)) := rfl
    refine Fin.ext ?_
    rw [hit, v0]
    all_goals omega
  by_cases hc38 : k.val = m + 2 * (m / 3) + 1
  · have hts : ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = 5 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    refine ⟨(((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)), 1, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inr (Or.inr (⟨by omega, by omega⟩)))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have hit : (sigF 2 m)^[1] (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))) := rfl
    refine Fin.ext ?_
    rw [hit, v1]
    all_goals omega
  by_cases hc39 : k.val = m - 10
  · have hts : ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = 5 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    refine ⟨(((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)), 2, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inr (Or.inr (⟨by omega, by omega⟩)))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))))).val = m - 10 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have hit : (sigF 2 m)^[2] (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))) := rfl
    refine Fin.ext ?_
    rw [hit, v2]
    all_goals omega
  by_cases hc40 : k.val = m - 9
  · have hts : ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = 5 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    refine ⟨(((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)), 3, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inr (Or.inr (⟨by omega, by omega⟩)))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))))).val = m - 10 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))))).val = m - 9 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have hit : (sigF 2 m)^[3] (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))))) := rfl
    refine Fin.ext ?_
    rw [hit, v3]
    all_goals omega
  by_cases hc41 : k.val = m - 8
  · have hts : ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = m / 3 - 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have hlen : lenL m ((((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = 5 := by
      rw [hts]
      exact lenL_eq hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    refine ⟨(((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)), 4, by omega, ?_⟩
    have v0 : (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))).val = m + (m / 3) := by
      rw [iota_val hm, hts]
      exact iota2_eq hm (Or.inr (Or.inr (⟨by omega, by omega⟩)))
    have v1 : (sigF 2 m (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))).val = m + 2 * (m / 3) + 1 := by
      rw [sigF_val hm12 he h3, sigNat_two, v0]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))
    have v2 : (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))))).val = m - 10 := by
      rw [sigF_val hm12 he h3, sigNat_two, v1]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega⟩)))))))))))
    have v3 : (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))))).val = m - 9 := by
      rw [sigF_val hm12 he h3, sigNat_two, v2]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have v4 : (sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1))))))).val = m - 8 := by
      rw [sigF_val hm12 he h3, sigNat_two, v3]
      exact sig2_eq hm12 he h3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
    have hit : (sigF 2 m)^[4] (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))
        = sigF 2 m (sigF 2 m (sigF 2 m (sigF 2 m (iota 2 m (((m / 3 - 2 : Nat)) : ZMod (m / 3 - 1)))))) := rfl
    refine Fin.ext ?_
    rw [hit, v4]
    all_goals omega
  exfalso
  omega

/-! ## Every drift ray meets the active seam -/

section RayHits

variable {m : Nat} [NeZero m]

private theorem memP_zero_cpt (hm : 4 ≤ m) {x y : Nat}
    (hx : ((x : Nat) : ZMod m).val = 0)
    (hy : ((y : Nat) : ZMod m).val = 0) :
    memP (cpt x y : TerminalQ m) := by
  refine Or.inl ?_
  show (((x : Nat) : ZMod m), ((y : Nat) : ZMod m))
      = ((0 : ZMod m), (0 : ZMod m))
  rw [Prod.mk.injEq]
  exact ⟨(ZMod.val_eq_zero _).mp hx, (ZMod.val_eq_zero _).mp hy⟩

/-- Anti-diagonal membership from an explicit multiple-of-`m` coordinate
sum (`omega` cannot reason about `% m` with a variable modulus, so the
multiple is enumerated). -/
private theorem memP_anti_cpt (hm : 4 ≤ m) {x y : Nat}
    (hsum : x + y = 1 * m ∨ x + y = 2 * m ∨ x + y = 3 * m ∨
      x + y = 4 * m ∨ x + y = 5 * m ∨ x + y = 6 * m ∨
      x + y = 7 * m ∨ x + y = 8 * m)
    (hx : 3 ≤ ((x : Nat) : ZMod m).val) : memP (cpt x y : TerminalQ m) := by
  refine Or.inr (Or.inl ⟨?_, hx⟩)
  show ((x : Nat) : ZMod m) + ((y : Nat) : ZMod m) = 0
  rw [show ((x : Nat) : ZMod m) + ((y : Nat) : ZMod m)
      = ((x + y : Nat) : ZMod m) by push_cast; ring]
  rcases hsum with h | h | h | h | h | h | h | h <;>
    (rw [h]; push_cast [ZMod.natCast_self]; ring)

private theorem memP_patch2_cpt (hm : 4 ≤ m) {x y : Nat}
    (hx : ((x : Nat) : ZMod m).val = 2)
    (hy : ((y : Nat) : ZMod m).val = m - 1) :
    memP (cpt x y : TerminalQ m) := by
  refine Or.inr (Or.inr (Or.inr ?_))
  show (((x : Nat) : ZMod m), ((y : Nat) : ZMod m))
      = ((2 : ZMod m), (-1 : ZMod m))
  rw [Prod.mk.injEq]
  constructor
  · have h2 : (((2 : Nat)) : ZMod m).val = 2 := valNat_lt (by omega)
    have hxx := ZMod.val_injective m (hx.trans h2.symm)
    rw [hxx]
    push_cast
    ring
  · have h2 : (((m - 1 : Nat)) : ZMod m).val = m - 1 := valNat_lt (by omega)
    exact (ZMod.val_injective m (hy.trans h2.symm)).trans
      (neg_one_cast hm).symm

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

private theorem memQ_patch2_cpt (hm : 4 ≤ m) {x y : Nat}
    (hx : ((x : Nat) : ZMod m) = ((2 : Nat) : ZMod m))
    (hy : ((y : Nat) : ZMod m).val = m - 2) :
    memQ (cpt x y : TerminalQ m) := by
  refine Or.inr (Or.inr ?_)
  show (((x : Nat) : ZMod m), ((y : Nat) : ZMod m))
      = ((2 : ZMod m), (-2 : ZMod m))
  rw [Prod.mk.injEq]
  constructor
  · rw [hx]
    push_cast
    ring
  · have h2 : (((m - 2 : Nat)) : ZMod m).val = m - 2 := valNat_lt (by omega)
    exact (ZMod.val_injective m (hy.trans h2.symm)).trans
      (neg_two_cast hm).symm

private theorem memS_patch1_cpt (hm : 4 ≤ m) {x y : Nat}
    (hx : ((x : Nat) : ZMod m).val = 1)
    (hy : ((y : Nat) : ZMod m).val = m - 1) :
    memS (cpt x y : TerminalQ m) := by
  refine Or.inr (Or.inl ?_)
  show (((x : Nat) : ZMod m), ((y : Nat) : ZMod m))
      = ((1 : ZMod m), (-1 : ZMod m))
  rw [Prod.mk.injEq]
  constructor
  · have h1 : (((1 : Nat)) : ZMod m).val = 1 := valNat_lt (by omega)
    have hxx := ZMod.val_injective m (hx.trans h1.symm)
    rw [hxx]
    push_cast
    ring
  · have h1 : (((m - 1 : Nat)) : ZMod m).val = m - 1 := valNat_lt (by omega)
    exact (ZMod.val_injective m (hy.trans h1.symm)).trans
      (neg_one_cast hm).symm

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

/-- Color 0 (`u₀ = (m−4, 1)`): ride to the row `y = −1`; landing `x = 2` is
the `P` patch `(2, −1)`, the only inactive landing `x = 1` is fixed by
riding `m/3` further onto the `P` anti-diagonal (the sum `x + y` is
invariant mod `3` along the ray, and `x = 1` forces it `≡ 0`). -/
private theorem hit0 {m : Nat} [NeZero m] (hm : 12 ≤ m) (he : m % 2 = 0)
    (h3 : m % 3 = 0) (w : TerminalQ m) :
    ∃ j : Nat, activePred 0 (w + j • uVec m 0) := by
  have hm4 : 4 ≤ m := by omega
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_cpt_rep w
  have hx1 := val_cases6m (m := m)
    (a := a + 4 * (m - (m - 1 - b))) (by omega)
  by_cases h2 : ((a + 4 * (m - (m - 1 - b)) : Nat) : ZMod m).val = 2
  · refine ⟨m - 1 - b, ?_⟩
    rw [cpt_add_u0 hm _ _ (m - 1 - b) (by omega)]
    refine Or.inl (memP_patch2_cpt hm4 h2 ?_)
    rw [show b + (m - 1 - b) = m - 1 by omega]
    exact valNat_lt (by omega)
  by_cases h1 : ((a + 4 * (m - (m - 1 - b)) : Nat) : ZMod m).val = 1
  · by_cases hbig : m - 1 - b + m / 3 ≤ m
    · refine ⟨m - 1 - b + m / 3, ?_⟩
      rw [cpt_add_u0 hm _ _ (m - 1 - b + m / 3) (by omega)]
      have hx2 := val_cases6m (m := m)
        (a := a + 4 * (m - (m - 1 - b + m / 3))) (by omega)
      exact Or.inl (memP_anti_cpt hm4 (by omega) (by omega))
    · refine ⟨m / 3 - 1 - b, ?_⟩
      rw [cpt_add_u0 hm _ _ (m / 3 - 1 - b) (by omega)]
      have hx2 := val_cases6m (m := m)
        (a := a + 4 * (m - (m / 3 - 1 - b))) (by omega)
      exact Or.inl (memP_anti_cpt hm4 (by omega) (by omega))
  · refine ⟨m - 1 - b, ?_⟩
    rw [cpt_add_u0 hm _ _ (m - 1 - b) (by omega)]
    refine Or.inr (memQ_row_cpt hm4 ?_ (by omega))
    rw [show b + (m - 1 - b) = m - 1 by omega]
    exact valNat_lt (by omega)

/-- Color 1 (`u₁ = (3, m−4)`): the coordinate sum drops by `1` per step, so
ride to the `P` anti-diagonal; landings `x = 0` and `x = 1` are the active
patches `(0,0) ∈ P` and `(1, −1) ∈ S`, and the only inactive landing
`x = 2` (the `Q` patch `(2, −2)`) is fixed by riding `m/3` further onto the
`S` column `x = 2` at depth `2m/3 − 2 ≤ m − 3`. -/
private theorem hit1_aux {m : Nat} [NeZero m] (hm : 12 ≤ m)
    (he : m % 2 = 0) (h3 : m % 3 = 0) (a b j0 : Nat) (ha : a < m)
    (hb : b < m) (hj : j0 < m ∧ (a + b = j0 ∨ a + b = j0 + m)) :
    ∃ j : Nat, activePred 1 ((cpt a b : TerminalQ m) + j • uVec m 1) := by
  have hm4 : 4 ≤ m := by omega
  have hxv := val_cases4m (m := m) (a := a + 3 * j0) (by omega)
  by_cases h2 : ((a + 3 * j0 : Nat) : ZMod m).val = 2
  · by_cases hbig : j0 + m / 3 ≤ m
    · refine ⟨j0 + m / 3, ?_⟩
      rw [cpt_add_u1 hm _ _ (j0 + m / 3) (by omega)]
      have hyv := val_cases6m (m := m)
        (a := b + 4 * (m - (j0 + m / 3))) (by omega)
      exact Or.inr (memS_col_cpt hm4 (castMod (by omega)) (by omega))
    · refine ⟨j0 + m / 3 - m, ?_⟩
      rw [cpt_add_u1 hm _ _ (j0 + m / 3 - m) (by omega)]
      have hxv2 := val_cases4m (m := m)
        (a := a + 3 * (j0 + m / 3 - m)) (by omega)
      have hyv := val_cases6m (m := m)
        (a := b + 4 * (m - (j0 + m / 3 - m))) (by omega)
      exact Or.inr (memS_col_cpt hm4 (castMod (by omega)) (by omega))
  · refine ⟨j0, ?_⟩
    rw [cpt_add_u1 hm _ _ j0 (by omega)]
    have hyv := val_cases6m (m := m) (a := b + 4 * (m - j0)) (by omega)
    by_cases h1 : ((a + 3 * j0 : Nat) : ZMod m).val = 1
    · exact Or.inr (memS_patch1_cpt hm4 h1 (by omega))
    by_cases h0 : ((a + 3 * j0 : Nat) : ZMod m).val = 0
    · exact Or.inl (memP_zero_cpt hm4 h0 (by omega))
    · exact Or.inl (memP_anti_cpt hm4 (by omega) (by omega))

/-- Color 1 (`u₁ = (3, m−4)`): the coordinate sum drops by `1` per step, so
ride to the `P` anti-diagonal; landings `x = 0` and `x = 1` are the active
patches `(0,0) ∈ P` and `(1, −1) ∈ S`, and the only inactive landing
`x = 2` (the `Q` patch `(2, −2)`) is fixed by riding `m/3` further onto the
`S` column `x = 2` at depth `2m/3 − 2 ≤ m − 3`. -/
private theorem hit1 {m : Nat} [NeZero m] (hm : 12 ≤ m) (he : m % 2 = 0)
    (h3 : m % 3 = 0) (w : TerminalQ m) :
    ∃ j : Nat, activePred 1 (w + j • uVec m 1) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_cpt_rep w
  by_cases hab : a + b < m
  · exact hit1_aux hm he h3 a b (a + b) ha hb ⟨by omega, by omega⟩
  · exact hit1_aux hm he h3 a b (a + b - m) ha hb ⟨by omega, by omega⟩

/-- Color 2 (`u₂ = (1, 3)`): ride to the column `x = 2`; landing depth
`m − 2` is the `Q` patch `(2, −2)`, and the only inactive landing depth
`m − 1` is fixed by riding `m/3` further onto the `Q` row `y = −1` at
abscissa `2 + m/3 ≥ 3`. -/
private theorem hit2 {m : Nat} [NeZero m] (hm : 12 ≤ m) (he : m % 2 = 0)
    (h3 : m % 3 = 0) (w : TerminalQ m) :
    ∃ j : Nat, activePred 2 (w + j • uVec m 2) := by
  have hm4 : 4 ≤ m := by omega
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_cpt_rep w
  by_cases ha2 : a ≤ 2
  · have hyv := val_cases4m (m := m) (a := b + 3 * (2 - a)) (by omega)
    by_cases hbad : ((b + 3 * (2 - a) : Nat) : ZMod m).val = m - 1
    · refine ⟨2 - a + m / 3, ?_⟩
      rw [cpt_add_u2 hm _ _ (2 - a + m / 3)]
      have hxv := val_cases4m (m := m)
        (a := a + (2 - a + m / 3)) (by omega)
      have hyv2 := val_cases6m (m := m)
        (a := b + 3 * (2 - a + m / 3)) (by omega)
      exact Or.inl (memQ_row_cpt hm4 (by omega) (by omega))
    by_cases hbad2 : ((b + 3 * (2 - a) : Nat) : ZMod m).val = m - 2
    · refine ⟨2 - a, ?_⟩
      rw [cpt_add_u2 hm _ _ (2 - a)]
      exact Or.inl (memQ_patch2_cpt hm4 (castMod (by omega)) (by omega))
    · refine ⟨2 - a, ?_⟩
      rw [cpt_add_u2 hm _ _ (2 - a)]
      exact Or.inr (memS_col_cpt hm4 (castMod (by omega)) (by omega))
  · have hyv := val_cases4m (m := m) (a := b + 3 * (2 + m - a)) (by omega)
    by_cases hbad : ((b + 3 * (2 + m - a) : Nat) : ZMod m).val = m - 1
    · refine ⟨2 + m - a + m / 3, ?_⟩
      rw [cpt_add_u2 hm _ _ (2 + m - a + m / 3)]
      have hxv := val_cases4m (m := m)
        (a := a + (2 + m - a + m / 3)) (by omega)
      have hyv2 := val_cases6m (m := m)
        (a := b + 3 * (2 + m - a + m / 3)) (by omega)
      exact Or.inl (memQ_row_cpt hm4 (by omega) (by omega))
    by_cases hbad2 : ((b + 3 * (2 + m - a) : Nat) : ZMod m).val = m - 2
    · refine ⟨2 + m - a, ?_⟩
      rw [cpt_add_u2 hm _ _ (2 + m - a)]
      exact Or.inl (memQ_patch2_cpt hm4 (castMod (by omega)) (by omega))
    · refine ⟨2 + m - a, ?_⟩
      rw [cpt_add_u2 hm _ _ (2 + m - a)]
      exact Or.inr (memS_col_cpt hm4 (castMod (by omega)) (by omega))

end RayHits

/-! ## The label successor is a single `2m`-cycle -/

/-- The `m = 12` level-2 exception: `σ_c`'s orbit rank tables on the `24`
labels (`scripts/search_d3_even_dir.py core3dvd --m 12`). -/
private def rankSig12 : Fin 3 → List (ZMod 24)
  | 0 => [0, 5, 18, 7, 12, 1, 6, 19, 8, 13, 2, 15, 16, 17, 14, 3, 4, 9,
      10, 23, 20, 21, 22, 11]
  | 1 => [0, 1, 14, 3, 8, 21, 10, 15, 4, 9, 22, 11, 16, 5, 18, 19, 20,
      17, 6, 7, 12, 13, 2, 23]
  | 2 => [0, 1, 22, 11, 12, 17, 18, 7, 4, 5, 6, 19, 8, 13, 2, 15, 20, 9,
      14, 3, 16, 21, 10, 23]

private def rank12 (c : Fin 3) (k : Fin (2 * 12)) : ZMod 24 :=
  (rankSig12 c).getD k.val 0

private theorem sig12_singleCycle (c : Fin 3) :
    IsSingleCycleMap (sigF c 12) := by
  refine Shared.single_cycle_of_zmod_rank _ (rank12 c) ?_ ?_ <;>
    rcases fin3_cases c with rfl | rfl | rfl <;> decide

/-- `σ_c` is a single `2m`-cycle for every even `3 ∣ m`, `m ≥ 12`: the
generic case is the `+2` transversal splice (`m ≥ 18`); `m = 12` is the
orbit-rank certificate. -/
private theorem sigF_singleCycle {m : Nat} [NeZero m] (hm : 12 ≤ m)
    (he : m % 2 = 0) (h3 : m % 3 = 0) (c : Fin 3) :
    IsSingleCycleMap (sigF c m) := by
  by_cases h12 : m = 12
  · subst h12
    exact sig12_singleCycle c
  have hm18 : 18 ≤ m := by omega
  haveI : NeZero (m / 3 - 1) := ⟨by omega⟩
  have hcop : Nat.Coprime 2 (m / 3 - 1) :=
    Nat.coprime_two_left.mpr ⟨(m / 3 - 2) / 2, by omega⟩
  have hchain : ∀ t : ZMod (m / 3 - 1),
      (sigF c m)^[lenL m t.val] (iota c m t) = iota c m (t + 2) := by
    rcases fin3_cases c with rfl | rfl | rfl
    · exact chain0 hm18 he h3
    · exact chain1 hm18 he h3
    · exact chain2 hm18 he h3
  have hcover : ∀ k : Fin (2 * m), ∃ t : ZMod (m / 3 - 1), ∃ j : Nat,
      j < lenL m t.val ∧ (sigF c m)^[j] (iota c m t) = k := by
    rcases fin3_cases c with rfl | rfl | rfl
    · exact cover0 hm18 he h3
    · exact cover1 hm18 he h3
    · exact cover2 hm18 he h3
  exact single_cycle_of_interval_splice (sigF c m)
    (fun t : ZMod (m / 3 - 1) => t + 2) (iota c m)
    (fun t => lenL m t.val) (fun t => lenL_pos hm18 t.val)
    hchain (addTwo_singleCycle _ hcop) hcover

/-! ## Assembly: the per-color core single cycles -/

section Assembly

/-- The level-1 splice: for even `3 ∣ m` with `m ≥ 12` the core map
`G_c = T_{u_c} ∘ ρ_c` is a single `m²`-cycle on `Q_m`. -/
private theorem coreMap_singleCycle {m : Nat} [NeZero m] (hm : 12 ≤ m)
    (he : m % 2 = 0) (h3 : m % 3 = 0) (c : Fin 3) :
    IsSingleCycleMap (coreMap c m) := by
  have hspec : ∀ k, SpecAt c m k := by
    rcases fin3_cases c with rfl | rfl | rfl
    · exact spec0 hm he h3
    · exact spec1 hm he h3
    · exact spec2 hm he h3
  have hhit : ∀ w : TerminalQ m, ∃ j : Nat,
      activePred c (w + j • uVec m c) := by
    rcases fin3_cases c with rfl | rfl | rfl
    · exact hit0 hm he h3
    · exact hit1 hm he h3
    · exact hit2 hm he h3
  exact single_cycle_of_interval_splice (coreMap c m) (sigF c m)
    (headF c m) (fun k => lenNat c m k.val) (lenF_pos hm he h3 c)
    (traverse_of_spec hm he h3 c hspec)
    (sigF_singleCycle hm he h3 c)
    (cover_of_spec hm he h3 c hspec
      (sigF_singleCycle hm he h3 c).1.2 hhit)

/-! ### The `m = 6` orbit certificate

The only even `3 ∣ m` modulus below `12`.  The three orbit rank tables are
the `G_c`-orbits of `(0,0)` printed by
`scripts/search_d3_even_dir.py core3dvd --m 6` (index `6x + y`). -/

private def rankTbl6 : Fin 3 → List (ZMod 36)
  | 0 => [0, 26, 11, 22, 29, 14, 15, 5, 1, 33, 8, 19, 9, 16, 27, 12, 23,
      30, 20, 31, 6, 2, 34, 24, 25, 10, 17, 28, 13, 3, 4, 21, 32, 7, 18,
      35]
  | 1 => [0, 25, 19, 23, 17, 21, 10, 4, 8, 2, 27, 6, 14, 29, 33, 12, 31,
      35, 18, 22, 16, 26, 20, 24, 7, 1, 11, 5, 9, 3, 32, 15, 30, 34, 13,
      28]
  | 2 => [0, 21, 10, 31, 16, 26, 32, 17, 6, 1, 22, 11, 2, 23, 27, 12, 18,
      7, 28, 13, 8, 33, 3, 24, 34, 19, 4, 29, 14, 9, 30, 15, 25, 35, 20,
      5]

private def rank6 (c : Fin 3) (w : TerminalQ 6) : ZMod 36 :=
  (rankTbl6 c).getD (w.1.val * 6 + w.2.val) 0

private theorem core6_singleCycle (c : Fin 3) :
    IsSingleCycleMap
      (fun w : TerminalQ 6 => rho c w + driftPair 6 c) := by
  refine Shared.single_cycle_of_zmod_rank _ (rank6 c) ?_ ?_ <;>
    rcases fin3_cases c with rfl | rfl | rfl <;> decide

/-- The pair-coordinate core statement, all even `m ≥ 4` with `3 ∣ m`. -/
private theorem corePair_singleCycle {m : Nat} [NeZero m] (hm : 4 ≤ m)
    (hEven : Even m) (h3 : m % 3 = 0) (c : Fin 3) :
    IsSingleCycleMap
      (fun w : TerminalQ m => rho c w + driftPair m c) := by
  have he : m % 2 = 0 := Nat.even_iff.mp hEven
  by_cases h6 : m = 6
  · subst h6
    exact core6_singleCycle c
  · have hm12 : 12 ≤ m := by omega
    have hcm : (fun w : TerminalQ m => rho c w + driftPair m c)
        = coreMap c m := by
      funext w
      show rho c w + driftPair m c = rho c w + uVec m c
      rw [driftPair_eq_uVec hm h3 c]
    rw [hcm]
    exact coreMap_singleCycle hm12 he h3 c

end Assembly

/-! ## The root-section core statement -/

/-- **The `3 ∣ m` core cyclicity** (module 3b deliverable): for every even
`m ≥ 4` with `3 ∣ m` and every color, the conjugated core map
`w ↦ ρ_c(w) + u_c` of the rail-seam schedule is a single `m²`-cycle on the
standard root section.  Feeds `railReturn_singleCycle_of_core` /
`railCycleData` of module 2.

Hypothesis audit: `3 ∣ m` is used for the drift table (`driftPair` branches
on `m % 3`) and for the mod-3 residue classes of the label successor;
evenness enters exactly once in the generic argument, through the level-2
step `+2` generating `ZMod (m/3 − 1)` (`m/3` even makes `m/3 − 1` odd);
`4 ≤ m` fixes the seam geometry (module 1) and `m = 6`, `m = 12` are the
small exceptions closed by orbit-rank `decide` certificates. -/
theorem railCore_singleCycle_of_dvd (m : Nat) [NeZero m] (hm : 4 ≤ m)
    (hEven : Even m) (h3 : m % 3 = 0) (c : Fin 3) :
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
def railCycleData_of_dvd (m : Nat) [NeZero m] (hm : 4 ≤ m)
    (hEven : Even m) (h3 : m % 3 = 0) :
    RootFlatCycle.RootFlatCycleData 2 m :=
  railCycleData m hm
    (railCore_singleCycle_of_dvd m hm hEven h3 0)
    (railCore_singleCycle_of_dvd m hm hEven h3 1)
    (railCore_singleCycle_of_dvd m hm hEven h3 2)

/-! ## Decide anchors

The closed-form label successor and length tables against
`scripts/search_d3_even_dir.py core3dvd --m {12,18}` (the script is ground
truth). -/

section Anchors

example : (List.range 24).map (sig0 12)
    = [5, 6, 7, 8, 9, 10, 3, 20, 17, 14, 15, 12, 13, 2, 11, 16, 1, 18,
      23, 0, 21, 22, 19, 4] := by decide

example : (List.range 24).map (len0 12)
    = [4, 4, 4, 4, 4, 4, 8, 3, 2, 1, 1, 12, 12, 3, 11, 12, 2, 12, 1, 1,
      12, 12, 11, 4] := by decide

example : (List.range 24).map (sig1 12)
    = [1, 22, 7, 8, 9, 10, 11, 12, 13, 6, 23, 20, 17, 18, 15, 16, 5, 14,
      19, 4, 21, 2, 3, 0] := by decide

example : (List.range 24).map (len1 12)
    = [12, 11, 4, 4, 4, 4, 4, 4, 4, 8, 3, 2, 1, 1, 12, 12, 3, 11, 12, 2,
      12, 1, 1, 12] := by decide

example : (List.range 24).map (sig2 12)
    = [1, 14, 23, 4, 13, 6, 11, 12, 9, 10, 7, 16, 17, 18, 19, 20, 21,
      22, 15, 8, 5, 2, 3, 0] := by decide

example : (List.range 24).map (len2 12)
    = [12, 3, 11, 12, 2, 12, 1, 1, 12, 12, 11, 4, 4, 4, 4, 4, 4, 4, 8,
      3, 2, 1, 1, 12] := by decide

example : (List.range 36).map (sig0 18)
    = [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 5, 32, 29, 26, 23, 20, 21,
      18, 19, 4, 17, 22, 3, 24, 25, 2, 27, 28, 1, 30, 35, 0, 33, 34, 31,
      6] := by decide

example : (List.range 36).map (len0 18)
    = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 12, 5, 4, 3, 2, 1, 1, 18, 18, 5,
      17, 18, 4, 18, 18, 3, 18, 18, 2, 18, 1, 1, 18, 18, 17, 6] := by
  decide

example : (List.range 36).map (sig1 18)
    = [1, 34, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 8, 35, 32, 29,
      26, 23, 24, 21, 22, 7, 20, 25, 6, 27, 28, 5, 30, 31, 4, 33, 2, 3,
      0] := by decide

example : (List.range 36).map (sig2 18)
    = [1, 22, 35, 4, 21, 6, 7, 20, 9, 10, 19, 12, 17, 18, 15, 16, 13,
      24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 23, 14, 11, 8, 5, 2,
      3, 0] := by decide

-- The level-2 transversal and its lengths at m = 18
-- (iota skips d−4 = 2 and d−1 = 5; lengths (11, 7, 7, 6, 5)).
example : (List.range 5).map (iotaNat 0 18) = [0, 1, 3, 4, 6] := by decide

example : (List.range 5).map (lenL 18) = [11, 7, 7, 6, 5] := by decide

-- Sample of the m = 6 rank step: the full step law is part of
-- `core6_singleCycle` above.
example :
    rank6 0 (rho 0 ((0 : ZMod 6), (0 : ZMod 6)) + driftPair 6 0) = 1 ∧
      rank6 1 (rho 1 ((2 : ZMod 6), (3 : ZMod 6)) + driftPair 6 1)
        = rank6 1 ((2 : ZMod 6), (3 : ZMod 6)) + 1 := by decide

end Anchors

end D3EvenRailCore3Dvd
end V28Hard
end EvenV11
