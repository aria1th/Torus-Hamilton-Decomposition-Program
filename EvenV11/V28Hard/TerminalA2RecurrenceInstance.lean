import EvenV11.V28Hard.TerminalA2EndpointRank

/-!
# Concrete terminal `A₂` endpoint recurrence instance

This file constructs the first concrete instance of
`D3TerminalA2Parametric.TerminalA2EndpointRecurrence m`: the paper's
per-fiber endpoint exchange `n_i`, together with proofs of all sixteen
recurrence fields for every modulus `m ≥ 6` (evenness is not needed).

The exchange swaps the two active endpoints inside each fiber of the
fiber label `ℓ_i` (`x` for color 0, `y` for color 1, `x+y` for color 2);
on the collision fibers `x = 2`, `y = 3`, and `x + y = 3` it swaps the
two puncture endpoints `E⁺_i ↔ E⁻_i` and fixes the collision point.

The final corollary feeds the instance into
`TerminalA2EndpointRank.compressedEndpointImageMap_singleCycle_of_recurrence`,
closing H1a's recurrence-instance obligation: for every even `m ≥ 6` the
compressed endpoint return is a single cycle on each active endpoint image.
-/

namespace EvenV11
namespace V28Hard
namespace TerminalA2RecurrenceInstance

open Shared
open TerminalA2LowMod
open D3TerminalA2Parametric

/-! ## Small `ZMod` toolkit -/

private theorem natCast_ne_natCast {m : Nat} [NeZero m] {a b : Nat}
    (ha : a < m) (hb : b < m) (hne : a ≠ b) :
    ((a : ZMod m)) ≠ ((b : ZMod m)) := by
  intro h
  exact hne
    (Nat.ModEq.eq_of_lt_of_lt ((ZMod.natCast_eq_natCast_iff a b m).mp h)
      ha hb)

private theorem zNe01 {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    (0 : ZMod m) ≠ 1 := by
  have h := natCast_ne_natCast (m := m) (a := 0) (b := 1)
    (by omega) (by omega) (by omega)
  exact_mod_cast h

private theorem zNe02 {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    (0 : ZMod m) ≠ 2 := by
  have h := natCast_ne_natCast (m := m) (a := 0) (b := 2)
    (by omega) (by omega) (by omega)
  exact_mod_cast h

private theorem zNe12 {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    (1 : ZMod m) ≠ 2 := by
  have h := natCast_ne_natCast (m := m) (a := 1) (b := 2)
    (by omega) (by omega) (by omega)
  exact_mod_cast h

private theorem zNe13 {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    (1 : ZMod m) ≠ 3 := by
  have h := natCast_ne_natCast (m := m) (a := 1) (b := 3)
    (by omega) (by omega) (by omega)
  exact_mod_cast h

private theorem zNe23 {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    (2 : ZMod m) ≠ 3 := by
  have h := natCast_ne_natCast (m := m) (a := 2) (b := 3)
    (by omega) (by omega) (by omega)
  exact_mod_cast h

private theorem zNe34 {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    (3 : ZMod m) ≠ 4 := by
  have h := natCast_ne_natCast (m := m) (a := 3) (b := 4)
    (by omega) (by omega) (by omega)
  exact_mod_cast h

private theorem pair_ne_left {m : Nat} {x y a b : ZMod m} (h : x ≠ a) :
    ((x, y) : TerminalQ m) ≠ (a, b) :=
  fun he => h (congrArg Prod.fst he)

private theorem pair_ne_right {m : Nat} {x y a b : ZMod m} (h : y ≠ b) :
    ((x, y) : TerminalQ m) ≠ (a, b) :=
  fun he => h (congrArg Prod.snd he)

private theorem pair_eq {m : Nat} {x y a b : ZMod m}
    (h1 : x = a) (h2 : y = b) :
    ((x, y) : TerminalQ m) = (a, b) := by
  rw [h1, h2]

/-! ## The seven special points of `terminalOmega` -/

private theorem pPt {m : Nat} :
    (p : TerminalQ m) = ((1 : ZMod m), (2 : ZMod m)) := rfl

private theorem pSubEH {m : Nat} :
    (p - eH : TerminalQ m) = ((0 : ZMod m), (2 : ZMod m)) := by
  simp only [p, eH, q, Prod.mk_sub_mk]
  exact pair_eq (by ring) (by ring)

private theorem pAddEH {m : Nat} :
    (p + eH : TerminalQ m) = ((2 : ZMod m), (2 : ZMod m)) := by
  simp only [p, eH, q, Prod.mk_add_mk]
  exact pair_eq (by ring) (by ring)

private theorem pSubEV {m : Nat} :
    (p - eV : TerminalQ m) = ((1 : ZMod m), (1 : ZMod m)) := by
  simp only [p, eV, q, Prod.mk_sub_mk]
  exact pair_eq (by ring) (by ring)

private theorem pAddEV {m : Nat} :
    (p + eV : TerminalQ m) = ((1 : ZMod m), (3 : ZMod m)) := by
  simp only [p, eV, q, Prod.mk_add_mk]
  exact pair_eq (by ring) (by ring)

private theorem pSubED {m : Nat} :
    (p - eD : TerminalQ m) = ((2 : ZMod m), (1 : ZMod m)) := by
  simp only [p, eD, q, Prod.mk_sub_mk]
  exact pair_eq (by ring) (by ring)

private theorem pAddED {m : Nat} :
    (p + eD : TerminalQ m) = ((0 : ZMod m), (3 : ZMod m)) := by
  simp only [p, eD, q, Prod.mk_add_mk]
  exact pair_eq (by ring) (by ring)

/-! ## `terminalOmega` evaluation lemmas -/

private theorem omega_02 {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    terminalOmega (((0 : ZMod m), (2 : ZMod m)) : TerminalQ m)
      = TerminalRow.chiMinus := by
  have g1 : (((0 : ZMod m), (2 : ZMod m)) : TerminalQ m) ≠ p := by
    rw [pPt]; exact pair_ne_left (zNe01 hm)
  have g2 : (((0 : ZMod m), (2 : ZMod m)) : TerminalQ m) = p - eH := by
    rw [pSubEH]
  simp only [terminalOmega]
  rw [if_neg g1, if_pos g2]

private theorem omega_22 {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    terminalOmega (((2 : ZMod m), (2 : ZMod m)) : TerminalQ m)
      = TerminalRow.chiPlus := by
  have g1 : (((2 : ZMod m), (2 : ZMod m)) : TerminalQ m) ≠ p := by
    rw [pPt]; exact pair_ne_left ((zNe12 hm).symm)
  have g2 : (((2 : ZMod m), (2 : ZMod m)) : TerminalQ m) ≠ p - eH := by
    rw [pSubEH]; exact pair_ne_left ((zNe02 hm).symm)
  have g3 : (((2 : ZMod m), (2 : ZMod m)) : TerminalQ m) = p + eH := by
    rw [pAddEH]
  simp only [terminalOmega]
  rw [if_neg g1, if_neg g2, if_pos g3]

private theorem omega_11 {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    terminalOmega (((1 : ZMod m), (1 : ZMod m)) : TerminalQ m)
      = TerminalRow.chiPlus := by
  have g1 : (((1 : ZMod m), (1 : ZMod m)) : TerminalQ m) ≠ p := by
    rw [pPt]; exact pair_ne_right (zNe12 hm)
  have g2 : (((1 : ZMod m), (1 : ZMod m)) : TerminalQ m) ≠ p - eH := by
    rw [pSubEH]; exact pair_ne_left ((zNe01 hm).symm)
  have g3 : (((1 : ZMod m), (1 : ZMod m)) : TerminalQ m) ≠ p + eH := by
    rw [pAddEH]; exact pair_ne_left (zNe12 hm)
  have g4 : (((1 : ZMod m), (1 : ZMod m)) : TerminalQ m) = p - eV := by
    rw [pSubEV]
  simp only [terminalOmega]
  rw [if_neg g1, if_neg g2, if_neg g3, if_pos g4]

private theorem omega_13 {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    terminalOmega (((1 : ZMod m), (3 : ZMod m)) : TerminalQ m)
      = TerminalRow.chiMinus := by
  have g1 : (((1 : ZMod m), (3 : ZMod m)) : TerminalQ m) ≠ p := by
    rw [pPt]; exact pair_ne_right ((zNe23 hm).symm)
  have g2 : (((1 : ZMod m), (3 : ZMod m)) : TerminalQ m) ≠ p - eH := by
    rw [pSubEH]; exact pair_ne_left ((zNe01 hm).symm)
  have g3 : (((1 : ZMod m), (3 : ZMod m)) : TerminalQ m) ≠ p + eH := by
    rw [pAddEH]; exact pair_ne_left (zNe12 hm)
  have g4 : (((1 : ZMod m), (3 : ZMod m)) : TerminalQ m) ≠ p - eV := by
    rw [pSubEV]; exact pair_ne_right ((zNe13 hm).symm)
  have g5 : (((1 : ZMod m), (3 : ZMod m)) : TerminalQ m) = p + eV := by
    rw [pAddEV]
  simp only [terminalOmega]
  rw [if_neg g1, if_neg g2, if_neg g3, if_neg g4, if_pos g5]

private theorem omega_21 {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    terminalOmega (((2 : ZMod m), (1 : ZMod m)) : TerminalQ m)
      = TerminalRow.chiMinus := by
  have g1 : (((2 : ZMod m), (1 : ZMod m)) : TerminalQ m) ≠ p := by
    rw [pPt]; exact pair_ne_left ((zNe12 hm).symm)
  have g2 : (((2 : ZMod m), (1 : ZMod m)) : TerminalQ m) ≠ p - eH := by
    rw [pSubEH]; exact pair_ne_left ((zNe02 hm).symm)
  have g3 : (((2 : ZMod m), (1 : ZMod m)) : TerminalQ m) ≠ p + eH := by
    rw [pAddEH]; exact pair_ne_right (zNe12 hm)
  have g4 : (((2 : ZMod m), (1 : ZMod m)) : TerminalQ m) ≠ p - eV := by
    rw [pSubEV]; exact pair_ne_left ((zNe12 hm).symm)
  have g5 : (((2 : ZMod m), (1 : ZMod m)) : TerminalQ m) ≠ p + eV := by
    rw [pAddEV]; exact pair_ne_left ((zNe12 hm).symm)
  have g6 : (((2 : ZMod m), (1 : ZMod m)) : TerminalQ m) = p - eD := by
    rw [pSubED]
  simp only [terminalOmega]
  rw [if_neg g1, if_neg g2, if_neg g3, if_neg g4, if_neg g5, if_pos g6]

private theorem omega_03 {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    terminalOmega (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m)
      = TerminalRow.chiPlus := by
  have g1 : (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m) ≠ p := by
    rw [pPt]; exact pair_ne_left (zNe01 hm)
  have g2 : (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m) ≠ p - eH := by
    rw [pSubEH]; exact pair_ne_right ((zNe23 hm).symm)
  have g3 : (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m) ≠ p + eH := by
    rw [pAddEH]; exact pair_ne_left (zNe02 hm)
  have g4 : (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m) ≠ p - eV := by
    rw [pSubEV]; exact pair_ne_left (zNe01 hm)
  have g5 : (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m) ≠ p + eV := by
    rw [pAddEV]; exact pair_ne_left (zNe01 hm)
  have g6 : (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m) ≠ p - eD := by
    rw [pSubED]; exact pair_ne_left (zNe02 hm)
  have g7 : (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m) = p + eD := by
    rw [pAddED]
  simp only [terminalOmega]
  rw [if_neg g1, if_neg g2, if_neg g3, if_neg g4, if_neg g5, if_neg g6,
    if_pos g7]

private theorem omega_tau02 {m : Nat} [NeZero m] {w : TerminalQ m}
    (h1 : w ≠ ((1 : ZMod m), (2 : ZMod m)))
    (h2 : w ≠ ((0 : ZMod m), (2 : ZMod m)))
    (h3 : w ≠ ((2 : ZMod m), (2 : ZMod m)))
    (h4 : w ≠ ((1 : ZMod m), (1 : ZMod m)))
    (h5 : w ≠ ((1 : ZMod m), (3 : ZMod m)))
    (h6 : w ≠ ((2 : ZMod m), (1 : ZMod m)))
    (h7 : w ≠ ((0 : ZMod m), (3 : ZMod m)))
    (h8 : w.2 = (2 : ZMod m)) :
    terminalOmega w = TerminalRow.tau02 := by
  have g1 : w ≠ p := by rw [pPt]; exact h1
  have g2 : w ≠ p - eH := by rw [pSubEH]; exact h2
  have g3 : w ≠ p + eH := by rw [pAddEH]; exact h3
  have g4 : w ≠ p - eV := by rw [pSubEV]; exact h4
  have g5 : w ≠ p + eV := by rw [pAddEV]; exact h5
  have g6 : w ≠ p - eD := by rw [pSubED]; exact h6
  have g7 : w ≠ p + eD := by rw [pAddED]; exact h7
  simp only [terminalOmega]
  rw [if_neg g1, if_neg g2, if_neg g3, if_neg g4, if_neg g5, if_neg g6,
    if_neg g7, if_pos h8]

private theorem omega_tau12 {m : Nat} [NeZero m] {w : TerminalQ m}
    (h1 : w ≠ ((1 : ZMod m), (2 : ZMod m)))
    (h2 : w ≠ ((0 : ZMod m), (2 : ZMod m)))
    (h3 : w ≠ ((2 : ZMod m), (2 : ZMod m)))
    (h4 : w ≠ ((1 : ZMod m), (1 : ZMod m)))
    (h5 : w ≠ ((1 : ZMod m), (3 : ZMod m)))
    (h6 : w ≠ ((2 : ZMod m), (1 : ZMod m)))
    (h7 : w ≠ ((0 : ZMod m), (3 : ZMod m)))
    (h8 : w.2 ≠ (2 : ZMod m))
    (h9 : w.1 = (1 : ZMod m)) :
    terminalOmega w = TerminalRow.tau12 := by
  have g1 : w ≠ p := by rw [pPt]; exact h1
  have g2 : w ≠ p - eH := by rw [pSubEH]; exact h2
  have g3 : w ≠ p + eH := by rw [pAddEH]; exact h3
  have g4 : w ≠ p - eV := by rw [pSubEV]; exact h4
  have g5 : w ≠ p + eV := by rw [pAddEV]; exact h5
  have g6 : w ≠ p - eD := by rw [pSubED]; exact h6
  have g7 : w ≠ p + eD := by rw [pAddED]; exact h7
  simp only [terminalOmega]
  rw [if_neg g1, if_neg g2, if_neg g3, if_neg g4, if_neg g5, if_neg g6,
    if_neg g7, if_neg h8, if_pos h9]

private theorem omega_tau01 {m : Nat} [NeZero m] {w : TerminalQ m}
    (h1 : w ≠ ((1 : ZMod m), (2 : ZMod m)))
    (h2 : w ≠ ((0 : ZMod m), (2 : ZMod m)))
    (h3 : w ≠ ((2 : ZMod m), (2 : ZMod m)))
    (h4 : w ≠ ((1 : ZMod m), (1 : ZMod m)))
    (h5 : w ≠ ((1 : ZMod m), (3 : ZMod m)))
    (h6 : w ≠ ((2 : ZMod m), (1 : ZMod m)))
    (h7 : w ≠ ((0 : ZMod m), (3 : ZMod m)))
    (h8 : w.2 ≠ (2 : ZMod m))
    (h9 : w.1 ≠ (1 : ZMod m))
    (h10 : w.1 + w.2 = (3 : ZMod m)) :
    terminalOmega w = TerminalRow.tau01 := by
  have g1 : w ≠ p := by rw [pPt]; exact h1
  have g2 : w ≠ p - eH := by rw [pSubEH]; exact h2
  have g3 : w ≠ p + eH := by rw [pAddEH]; exact h3
  have g4 : w ≠ p - eV := by rw [pSubEV]; exact h4
  have g5 : w ≠ p + eV := by rw [pAddEV]; exact h5
  have g6 : w ≠ p - eD := by rw [pSubED]; exact h6
  have g7 : w ≠ p + eD := by rw [pAddED]; exact h7
  simp only [terminalOmega]
  rw [if_neg g1, if_neg g2, if_neg g3, if_neg g4, if_neg g5, if_neg g6,
    if_neg g7, if_neg h8, if_neg h9, if_pos h10]

/-! ## The endpoint exchange -/

private def exchange0 {m : Nat} (z : TerminalQ m) : TerminalQ m :=
  if z.1 = 2 then
    (if z.2 = 3 then (2, 1) else if z.2 = 1 then (2, 3) else z)
  else if z.2 = 2 then (z.1, 4 - z.1)
  else if z.2 = 4 - z.1 then (z.1, 2)
  else z

private def exchange1 {m : Nat} (z : TerminalQ m) : TerminalQ m :=
  if z.2 = 3 then
    (if z.1 = 0 then (2, 3) else if z.1 = 2 then (0, 3) else z)
  else if z.1 = 1 then (4 - z.2, z.2)
  else if z.1 = 4 - z.2 then (1, z.2)
  else z

private def exchange2 {m : Nat} (z : TerminalQ m) : TerminalQ m :=
  if z.1 + z.2 = 3 then
    (if z = ((2 : ZMod m), (1 : ZMod m)) then (0, 3)
     else if z = ((0 : ZMod m), (3 : ZMod m)) then (2, 1) else z)
  else if z.1 = 1 then (z.1 + z.2 - 2, 2)
  else if z.2 = 2 then (1, z.1 + z.2 - 1)
  else z

/-- The paper's per-fiber endpoint exchange `n_i`.  Color `i` acts inside the
fibers of the label `ℓ_i` (`x`, `y`, and `x+y` respectively): it swaps the two
active endpoints of each generic fiber, while on the collision fiber
(`x = 2`, `y = 3`, `x + y = 3`) it swaps `E⁺_i ↔ E⁻_i` and fixes the
collision point. -/
def terminalExchange {m : Nat} [NeZero m] :
    TorusColor 3 → TerminalQ m → TerminalQ m
  | 0 => exchange0
  | 1 => exchange1
  | _ => exchange2

private theorem terminalExchange_zero {m : Nat} [NeZero m] :
    terminalExchange (m := m) 0 = exchange0 := rfl

private theorem terminalExchange_one {m : Nat} [NeZero m] :
    terminalExchange (m := m) 1 = exchange1 := rfl

private theorem terminalExchange_two {m : Nat} [NeZero m] :
    terminalExchange (m := m) 2 = exchange2 := rfl

/-! ## Exchange on the active endpoints -/

private theorem exchangeA0 {m : Nat} [NeZero m] (hm : 6 ≤ m) (r : ZMod m) :
    exchange0 ((r, (2 : ZMod m)) : TerminalQ m)
      = ((r, 4 - r) : TerminalQ m) := by
  by_cases hr : r = 2
  · subst hr
    simp only [exchange0, if_true]
    rw [if_neg (zNe23 hm), if_neg ((zNe12 hm).symm)]
    exact pair_eq rfl (by ring)
  · simp only [exchange0, if_true]
    rw [if_neg hr]

private theorem exchangeB0 {m : Nat} [NeZero m] (hm : 6 ≤ m) (r : ZMod m) :
    exchange0 ((r, 4 - r) : TerminalQ m)
      = ((r, (2 : ZMod m)) : TerminalQ m) := by
  by_cases hr : r = 2
  · subst hr
    rw [show ((4 : ZMod m) - 2) = (2 : ZMod m) from by ring]
    simp only [exchange0, if_true]
    rw [if_neg (zNe23 hm), if_neg ((zNe12 hm).symm)]
  · simp only [exchange0, if_true]
    rw [if_neg hr,
      if_neg (show ¬((4 : ZMod m) - r = 2) from
        fun h => hr (by linear_combination -h))]

private theorem exchangeA1 {m : Nat} [NeZero m] (hm : 6 ≤ m) (r : ZMod m) :
    exchange1 (((1 : ZMod m), r) : TerminalQ m)
      = ((4 - r, r) : TerminalQ m) := by
  by_cases hr : r = 3
  · subst hr
    simp only [exchange1, if_true]
    rw [if_neg ((zNe01 hm).symm), if_neg (zNe12 hm)]
    exact pair_eq (by ring) rfl
  · simp only [exchange1, if_true]
    rw [if_neg hr]

private theorem exchangeB1 {m : Nat} [NeZero m] (hm : 6 ≤ m) (r : ZMod m) :
    exchange1 ((4 - r, r) : TerminalQ m)
      = (((1 : ZMod m), r) : TerminalQ m) := by
  by_cases hr : r = 3
  · subst hr
    rw [show ((4 : ZMod m) - 3) = (1 : ZMod m) from by ring]
    simp only [exchange1, if_true]
    rw [if_neg ((zNe01 hm).symm), if_neg (zNe12 hm)]
  · simp only [exchange1, if_true]
    rw [if_neg hr,
      if_neg (show ¬((4 : ZMod m) - r = 1) from
        fun h => hr (by linear_combination -h))]

private theorem exchangeA2 {m : Nat} [NeZero m] (hm : 6 ≤ m) (r : ZMod m) :
    exchange2 (((1 : ZMod m), r - 1) : TerminalQ m)
      = ((r - 2, (2 : ZMod m)) : TerminalQ m) := by
  by_cases hr : r = 3
  · subst hr
    rw [show ((3 : ZMod m) - 1) = (2 : ZMod m) from by ring]
    simp only [exchange2, if_true]
    rw [if_pos (show (1 : ZMod m) + 2 = 3 from by ring),
      if_neg (pair_ne_left (zNe12 hm)),
      if_neg (pair_ne_left ((zNe01 hm).symm))]
    exact pair_eq (by ring) rfl
  · simp only [exchange2, if_true]
    rw [if_neg (show ¬((1 : ZMod m) + (r - 1) = 3) from
        fun h => hr (by linear_combination h))]
    exact pair_eq (by ring) rfl

private theorem exchangeB2 {m : Nat} [NeZero m] (hm : 6 ≤ m) (r : ZMod m) :
    exchange2 ((r - 2, (2 : ZMod m)) : TerminalQ m)
      = (((1 : ZMod m), r - 1) : TerminalQ m) := by
  by_cases hr : r = 3
  · subst hr
    rw [show ((3 : ZMod m) - 2) = (1 : ZMod m) from by ring]
    simp only [exchange2, if_true]
    rw [if_pos (show (1 : ZMod m) + 2 = 3 from by ring),
      if_neg (pair_ne_left (zNe12 hm)),
      if_neg (pair_ne_left ((zNe01 hm).symm))]
    exact pair_eq rfl (by ring)
  · simp only [exchange2, if_true]
    rw [if_neg (show ¬((r - 2) + (2 : ZMod m) = 3) from
        fun h => hr (by linear_combination h)),
      if_neg (show ¬(r - 2 = (1 : ZMod m)) from
        fun h => hr (by linear_combination h))]
    exact pair_eq rfl (by ring)

/-- The exchange swaps `A_i(r)` to `B_i(r)` on every fiber. -/
theorem terminalExchange_endpointA {m : Nat} [NeZero m] (hm : 6 ≤ m)
    (c : TorusColor 3) (r : ZMod m) :
    terminalExchange c (terminalEndpointA (m := m) c r) =
      terminalEndpointB (m := m) c r := by
  fin_cases c
  · exact exchangeA0 hm r
  · exact exchangeA1 hm r
  · exact exchangeA2 hm r

/-- The exchange swaps `B_i(r)` back to `A_i(r)` on every fiber. -/
theorem terminalExchange_endpointB {m : Nat} [NeZero m] (hm : 6 ≤ m)
    (c : TorusColor 3) (r : ZMod m) :
    terminalExchange c (terminalEndpointB (m := m) c r) =
      terminalEndpointA (m := m) c r := by
  fin_cases c
  · exact exchangeB0 hm r
  · exact exchangeB1 hm r
  · exact exchangeB2 hm r

/-! ## Exchange at the six concrete boundary images -/

private theorem ex0_21 {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    exchange0 (((2 : ZMod m), (1 : ZMod m)) : TerminalQ m)
      = ((2 : ZMod m), (3 : ZMod m)) := by
  simp only [exchange0, if_true]
  rw [if_neg (zNe13 hm)]

private theorem ex0_23 {m : Nat} [NeZero m] :
    exchange0 (((2 : ZMod m), (3 : ZMod m)) : TerminalQ m)
      = ((2 : ZMod m), (1 : ZMod m)) := by
  simp only [exchange0, if_true]

private theorem ex1_23 {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    exchange1 (((2 : ZMod m), (3 : ZMod m)) : TerminalQ m)
      = ((0 : ZMod m), (3 : ZMod m)) := by
  simp only [exchange1, if_true]
  rw [if_neg ((zNe02 hm).symm)]

private theorem ex1_03 {m : Nat} [NeZero m] :
    exchange1 (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m)
      = ((2 : ZMod m), (3 : ZMod m)) := by
  simp only [exchange1, if_true]

private theorem ex2_21 {m : Nat} [NeZero m] :
    exchange2 (((2 : ZMod m), (1 : ZMod m)) : TerminalQ m)
      = ((0 : ZMod m), (3 : ZMod m)) := by
  simp only [exchange2, if_true]
  rw [if_pos (show (2 : ZMod m) + 1 = 3 from by ring)]

private theorem ex2_03 {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    exchange2 (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m)
      = ((2 : ZMod m), (1 : ZMod m)) := by
  simp only [exchange2, if_true]
  rw [if_pos (show (0 : ZMod m) + 3 = 3 from by ring),
    if_neg (pair_ne_left (zNe02 hm))]

private theorem ex2_22 {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    exchange2 (((2 : ZMod m), (2 : ZMod m)) : TerminalQ m)
      = ((1 : ZMod m), (3 : ZMod m)) := by
  simp only [exchange2, if_true]
  rw [if_neg (show ¬((2 : ZMod m) + 2 = 3) from
      fun h => zNe34 hm (by linear_combination -h)),
    if_neg ((zNe12 hm).symm)]
  exact pair_eq rfl (by ring)

/-! ## The six generic recurrence steps -/

private theorem genA0 {m : Nat} [NeZero m] (hm : 6 ≤ m) {r : ZMod m}
    (hr2 : r ≠ 2) (hr3 : r ≠ 3) :
    terminalCompressedEndpointReturn (m := m) terminalExchange 0
        (terminalEndpointA (m := m) 0 r) =
      terminalEndpointB (m := m) 0 (r - 1) := by
  have heta : terminalEta (m := m) 0 (terminalEndpointA (m := m) 0 r)
      = terminalEndpointA (m := m) 0 (r - 1) := by
    simp only [terminalEta]
    rw [show terminalEndpointA (m := m) 0 r - terminalVertex (m := m) 0
        = ((r - 1, (2 : ZMod m)) : TerminalQ m) from by
      simp only [terminalEndpointA, terminalVertex, a0, q, Prod.mk_sub_mk]
      exact pair_eq (by ring) (by ring)]
    have hidx : terminalVertex (m := m)
        (terminalRowEquiv
          (terminalOmega ((r - 1, (2 : ZMod m)) : TerminalQ m)) 0)
        = ((0 : ZMod m), (0 : ZMod m)) := by
      by_cases hr1 : r = 1
      · subst hr1
        rw [show (((1 : ZMod m) - 1, (2 : ZMod m)) : TerminalQ m)
            = (((0 : ZMod m), (2 : ZMod m)) : TerminalQ m) from
          pair_eq (by ring) rfl]
        rw [omega_02 hm]
        rfl
      · rw [omega_tau02
          (pair_ne_left fun h => hr2 (by linear_combination h))
          (pair_ne_left fun h => hr1 (by linear_combination h))
          (pair_ne_left fun h => hr3 (by linear_combination h))
          (pair_ne_right ((zNe12 hm).symm))
          (pair_ne_right (zNe23 hm))
          (pair_ne_right ((zNe12 hm).symm))
          (pair_ne_right (zNe23 hm))
          rfl]
        rfl
    rw [hidx]
    simp only [terminalEndpointA, Prod.mk_add_mk]
    exact pair_eq (by ring) (by ring)
  simp only [terminalCompressedEndpointReturn]
  rw [heta]
  exact terminalExchange_endpointA hm 0 (r - 1)

private theorem genB0 {m : Nat} [NeZero m] (hm : 6 ≤ m) {r : ZMod m}
    (hr2 : r ≠ 2) (hr3 : r ≠ 3) :
    terminalCompressedEndpointReturn (m := m) terminalExchange 0
        (terminalEndpointB (m := m) 0 r) =
      terminalEndpointA (m := m) 0 (r - 1) := by
  have heta : terminalEta (m := m) 0 (terminalEndpointB (m := m) 0 r)
      = terminalEndpointB (m := m) 0 (r - 1) := by
    simp only [terminalEta]
    rw [show terminalEndpointB (m := m) 0 r - terminalVertex (m := m) 0
        = ((r - 1, (4 : ZMod m) - r) : TerminalQ m) from by
      simp only [terminalEndpointB, terminalVertex, a0, q, Prod.mk_sub_mk]
      exact pair_eq (by ring) (by ring)]
    have hidx : terminalVertex (m := m)
        (terminalRowEquiv
          (terminalOmega ((r - 1, (4 : ZMod m) - r) : TerminalQ m)) 0)
        = ((0 : ZMod m), (1 : ZMod m)) := by
      by_cases hr1 : r = 1
      · subst hr1
        rw [show (((1 : ZMod m) - 1, (4 : ZMod m) - 1) : TerminalQ m)
            = (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m) from
          pair_eq (by ring) (by ring)]
        rw [omega_03 hm]
        rfl
      · rw [omega_tau01
          (pair_ne_left fun h => hr2 (by linear_combination h))
          (pair_ne_left fun h => hr1 (by linear_combination h))
          (pair_ne_left fun h => hr3 (by linear_combination h))
          (pair_ne_left fun h => hr2 (by linear_combination h))
          (pair_ne_left fun h => hr2 (by linear_combination h))
          (pair_ne_left fun h => hr3 (by linear_combination h))
          (pair_ne_left fun h => hr1 (by linear_combination h))
          (fun h => hr2 (by linear_combination -h))
          (fun h => hr2 (by linear_combination h))
          (by ring)]
        rfl
    rw [hidx]
    simp only [terminalEndpointB, Prod.mk_add_mk]
    exact pair_eq (by ring) (by ring)
  simp only [terminalCompressedEndpointReturn]
  rw [heta]
  exact terminalExchange_endpointB hm 0 (r - 1)

private theorem genA1 {m : Nat} [NeZero m] (hm : 6 ≤ m) {r : ZMod m}
    (hr3 : r ≠ 3) (hr4 : r ≠ 4) :
    terminalCompressedEndpointReturn (m := m) terminalExchange 1
        (terminalEndpointA (m := m) 1 r) =
      terminalEndpointB (m := m) 1 (r - 1) := by
  have heta : terminalEta (m := m) 1 (terminalEndpointA (m := m) 1 r)
      = terminalEndpointA (m := m) 1 (r - 1) := by
    simp only [terminalEta]
    rw [show terminalEndpointA (m := m) 1 r - terminalVertex (m := m) 1
        = (((1 : ZMod m), r - 1) : TerminalQ m) from by
      simp only [terminalEndpointA, terminalVertex, a1, q, Prod.mk_sub_mk]
      exact pair_eq (by ring) (by ring)]
    have hidx : terminalVertex (m := m)
        (terminalRowEquiv
          (terminalOmega (((1 : ZMod m), r - 1) : TerminalQ m)) 1)
        = ((0 : ZMod m), (0 : ZMod m)) := by
      by_cases hr2 : r = 2
      · subst hr2
        rw [show (((1 : ZMod m), (2 : ZMod m) - 1) : TerminalQ m)
            = (((1 : ZMod m), (1 : ZMod m)) : TerminalQ m) from
          pair_eq rfl (by ring)]
        rw [omega_11 hm]
        rfl
      · rw [omega_tau12
          (pair_ne_right fun h => hr3 (by linear_combination h))
          (pair_ne_left ((zNe01 hm).symm))
          (pair_ne_left (zNe12 hm))
          (pair_ne_right fun h => hr2 (by linear_combination h))
          (pair_ne_right fun h => hr4 (by linear_combination h))
          (pair_ne_left (zNe12 hm))
          (pair_ne_left ((zNe01 hm).symm))
          (fun h => hr3 (by linear_combination h))
          rfl]
        rfl
    rw [hidx]
    simp only [terminalEndpointA, Prod.mk_add_mk]
    exact pair_eq (by ring) (by ring)
  simp only [terminalCompressedEndpointReturn]
  rw [heta]
  exact terminalExchange_endpointA hm 1 (r - 1)

private theorem genB1 {m : Nat} [NeZero m] (hm : 6 ≤ m) {r : ZMod m}
    (hr3 : r ≠ 3) (hr4 : r ≠ 4) :
    terminalCompressedEndpointReturn (m := m) terminalExchange 1
        (terminalEndpointB (m := m) 1 r) =
      terminalEndpointA (m := m) 1 (r - 1) := by
  have heta : terminalEta (m := m) 1 (terminalEndpointB (m := m) 1 r)
      = terminalEndpointB (m := m) 1 (r - 1) := by
    simp only [terminalEta]
    rw [show terminalEndpointB (m := m) 1 r - terminalVertex (m := m) 1
        = (((4 : ZMod m) - r, r - 1) : TerminalQ m) from by
      simp only [terminalEndpointB, terminalVertex, a1, q, Prod.mk_sub_mk]
      exact pair_eq (by ring) (by ring)]
    have hidx : terminalVertex (m := m)
        (terminalRowEquiv
          (terminalOmega (((4 : ZMod m) - r, r - 1) : TerminalQ m)) 1)
        = ((1 : ZMod m), (0 : ZMod m)) := by
      by_cases hr2 : r = 2
      · subst hr2
        rw [show (((4 : ZMod m) - 2, (2 : ZMod m) - 1) : TerminalQ m)
            = (((2 : ZMod m), (1 : ZMod m)) : TerminalQ m) from
          pair_eq (by ring) (by ring)]
        rw [omega_21 hm]
        rfl
      · rw [omega_tau01
          (pair_ne_left fun h => hr3 (by linear_combination -h))
          (pair_ne_left fun h => hr4 (by linear_combination -h))
          (pair_ne_left fun h => hr2 (by linear_combination -h))
          (pair_ne_left fun h => hr3 (by linear_combination -h))
          (pair_ne_left fun h => hr3 (by linear_combination -h))
          (pair_ne_left fun h => hr2 (by linear_combination -h))
          (pair_ne_left fun h => hr4 (by linear_combination -h))
          (fun h => hr3 (by linear_combination h))
          (fun h => hr3 (by linear_combination -h))
          (by ring)]
        rfl
    rw [hidx]
    simp only [terminalEndpointB, Prod.mk_add_mk]
    exact pair_eq (by ring) (by ring)
  simp only [terminalCompressedEndpointReturn]
  rw [heta]
  exact terminalExchange_endpointB hm 1 (r - 1)

private theorem genA2 {m : Nat} [NeZero m] (hm : 6 ≤ m) {r : ZMod m}
    (hr2 : r ≠ 2) (hr3 : r ≠ 3) :
    terminalCompressedEndpointReturn (m := m) terminalExchange 2
        (terminalEndpointA (m := m) 2 r) =
      terminalEndpointB (m := m) 2 (r + 1) := by
  have heta : terminalEta (m := m) 2 (terminalEndpointA (m := m) 2 r)
      = terminalEndpointA (m := m) 2 (r + 1) := by
    simp only [terminalEta]
    rw [show terminalEndpointA (m := m) 2 r - terminalVertex (m := m) 2
        = (((1 : ZMod m), r - 1) : TerminalQ m) from by
      simp only [terminalEndpointA, terminalVertex, a2, q, Prod.mk_sub_mk]
      exact pair_eq (by ring) (by ring)]
    have hidx : terminalVertex (m := m)
        (terminalRowEquiv
          (terminalOmega (((1 : ZMod m), r - 1) : TerminalQ m)) 2)
        = ((0 : ZMod m), (1 : ZMod m)) := by
      by_cases hr4 : r = 4
      · subst hr4
        rw [show (((1 : ZMod m), (4 : ZMod m) - 1) : TerminalQ m)
            = (((1 : ZMod m), (3 : ZMod m)) : TerminalQ m) from
          pair_eq rfl (by ring)]
        rw [omega_13 hm]
        rfl
      · rw [omega_tau12
          (pair_ne_right fun h => hr3 (by linear_combination h))
          (pair_ne_left ((zNe01 hm).symm))
          (pair_ne_left (zNe12 hm))
          (pair_ne_right fun h => hr2 (by linear_combination h))
          (pair_ne_right fun h => hr4 (by linear_combination h))
          (pair_ne_left (zNe12 hm))
          (pair_ne_left ((zNe01 hm).symm))
          (fun h => hr3 (by linear_combination h))
          rfl]
        rfl
    rw [hidx]
    simp only [terminalEndpointA, Prod.mk_add_mk]
    exact pair_eq (by ring) (by ring)
  simp only [terminalCompressedEndpointReturn]
  rw [heta]
  exact terminalExchange_endpointA hm 2 (r + 1)

private theorem genB2 {m : Nat} [NeZero m] (hm : 6 ≤ m) {r : ZMod m}
    (hr2 : r ≠ 2) (hr3 : r ≠ 3) :
    terminalCompressedEndpointReturn (m := m) terminalExchange 2
        (terminalEndpointB (m := m) 2 r) =
      terminalEndpointA (m := m) 2 (r + 1) := by
  have heta : terminalEta (m := m) 2 (terminalEndpointB (m := m) 2 r)
      = terminalEndpointB (m := m) 2 (r + 1) := by
    simp only [terminalEta]
    rw [show terminalEndpointB (m := m) 2 r - terminalVertex (m := m) 2
        = ((r - 2, (2 : ZMod m)) : TerminalQ m) from by
      simp only [terminalEndpointB, terminalVertex, a2, q, Prod.mk_sub_mk]
      exact pair_eq (by ring) (by ring)]
    have hidx : terminalVertex (m := m)
        (terminalRowEquiv
          (terminalOmega ((r - 2, (2 : ZMod m)) : TerminalQ m)) 2)
        = ((1 : ZMod m), (0 : ZMod m)) := by
      by_cases hr4 : r = 4
      · subst hr4
        rw [show (((4 : ZMod m) - 2, (2 : ZMod m)) : TerminalQ m)
            = (((2 : ZMod m), (2 : ZMod m)) : TerminalQ m) from
          pair_eq (by ring) rfl]
        rw [omega_22 hm]
        rfl
      · rw [omega_tau02
          (pair_ne_left fun h => hr3 (by linear_combination h))
          (pair_ne_left fun h => hr2 (by linear_combination h))
          (pair_ne_left fun h => hr4 (by linear_combination h))
          (pair_ne_right ((zNe12 hm).symm))
          (pair_ne_right (zNe23 hm))
          (pair_ne_right ((zNe12 hm).symm))
          (pair_ne_right (zNe23 hm))
          rfl]
        rfl
    rw [hidx]
    simp only [terminalEndpointB, Prod.mk_add_mk]
    exact pair_eq (by ring) (by ring)
  simp only [terminalCompressedEndpointReturn]
  rw [heta]
  exact terminalExchange_endpointB hm 2 (r + 1)

/-! ## The twelve boundary bridges -/

private theorem b0_B3 {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    terminalCompressedEndpointReturn (m := m) terminalExchange 0
        (terminalEndpointB (m := m) 0 3) =
      terminalEndpointEplus (m := m) 0 := by
  have heta : terminalEta (m := m) 0 (terminalEndpointB (m := m) 0 3)
      = (((2 : ZMod m), (1 : ZMod m)) : TerminalQ m) := by
    simp only [terminalEta]
    rw [show terminalEndpointB (m := m) 0 3 - terminalVertex (m := m) 0
        = (((2 : ZMod m), (1 : ZMod m)) : TerminalQ m) from by
      simp only [terminalEndpointB, terminalVertex, a0, q, Prod.mk_sub_mk]
      exact pair_eq (by ring) (by ring)]
    rw [omega_21 hm,
      show terminalVertex (m := m)
          (terminalRowEquiv TerminalRow.chiMinus 0)
          = ((0 : ZMod m), (0 : ZMod m)) from rfl]
    rw [Prod.mk_add_mk]
    exact pair_eq (by ring) (by ring)
  simp only [terminalCompressedEndpointReturn]
  rw [heta, terminalExchange_zero, ex0_21 hm]
  rfl

private theorem b0_Ep {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    terminalCompressedEndpointReturn (m := m) terminalExchange 0
        (terminalEndpointEplus (m := m) 0) =
      terminalEndpointA (m := m) 0 1 := by
  have heta : terminalEta (m := m) 0 (terminalEndpointEplus (m := m) 0)
      = terminalEndpointB (m := m) 0 1 := by
    simp only [terminalEta]
    rw [show terminalEndpointEplus (m := m) 0 - terminalVertex (m := m) 0
        = (((1 : ZMod m), (3 : ZMod m)) : TerminalQ m) from by
      simp only [terminalEndpointEplus, terminalVertex, a0, q,
        Prod.mk_sub_mk]
      exact pair_eq (by ring) (by ring)]
    rw [omega_13 hm,
      show terminalVertex (m := m)
          (terminalRowEquiv TerminalRow.chiMinus 0)
          = ((0 : ZMod m), (0 : ZMod m)) from rfl]
    rw [Prod.mk_add_mk]
    simp only [terminalEndpointB]
    exact pair_eq (by ring) (by ring)
  simp only [terminalCompressedEndpointReturn]
  rw [heta]
  exact terminalExchange_endpointB hm 0 1

private theorem b0_A3 {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    terminalCompressedEndpointReturn (m := m) terminalExchange 0
        (terminalEndpointA (m := m) 0 3) =
      terminalEndpointEminus (m := m) 0 := by
  have heta : terminalEta (m := m) 0 (terminalEndpointA (m := m) 0 3)
      = (((2 : ZMod m), (3 : ZMod m)) : TerminalQ m) := by
    simp only [terminalEta]
    rw [show terminalEndpointA (m := m) 0 3 - terminalVertex (m := m) 0
        = (((2 : ZMod m), (2 : ZMod m)) : TerminalQ m) from by
      simp only [terminalEndpointA, terminalVertex, a0, q, Prod.mk_sub_mk]
      exact pair_eq (by ring) (by ring)]
    rw [omega_22 hm,
      show terminalVertex (m := m)
          (terminalRowEquiv TerminalRow.chiPlus 0)
          = ((0 : ZMod m), (1 : ZMod m)) from rfl]
    rw [Prod.mk_add_mk]
    exact pair_eq (by ring) (by ring)
  simp only [terminalCompressedEndpointReturn]
  rw [heta, terminalExchange_zero, ex0_23]
  rfl

private theorem b0_Em {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    terminalCompressedEndpointReturn (m := m) terminalExchange 0
        (terminalEndpointEminus (m := m) 0) =
      terminalEndpointB (m := m) 0 1 := by
  have heta : terminalEta (m := m) 0 (terminalEndpointEminus (m := m) 0)
      = terminalEndpointA (m := m) 0 1 := by
    simp only [terminalEta]
    rw [show terminalEndpointEminus (m := m) 0 - terminalVertex (m := m) 0
        = (((1 : ZMod m), (1 : ZMod m)) : TerminalQ m) from by
      simp only [terminalEndpointEminus, terminalVertex, a0, q,
        Prod.mk_sub_mk]
      exact pair_eq (by ring) (by ring)]
    rw [omega_11 hm,
      show terminalVertex (m := m)
          (terminalRowEquiv TerminalRow.chiPlus 0)
          = ((0 : ZMod m), (1 : ZMod m)) from rfl]
    rw [Prod.mk_add_mk]
    simp only [terminalEndpointA]
    exact pair_eq (by ring) (by ring)
  simp only [terminalCompressedEndpointReturn]
  rw [heta]
  exact terminalExchange_endpointA hm 0 1

private theorem b1_A4 {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    terminalCompressedEndpointReturn (m := m) terminalExchange 1
        (terminalEndpointA (m := m) 1 4) =
      terminalEndpointEplus (m := m) 1 := by
  have heta : terminalEta (m := m) 1 (terminalEndpointA (m := m) 1 4)
      = (((2 : ZMod m), (3 : ZMod m)) : TerminalQ m) := by
    simp only [terminalEta]
    rw [show terminalEndpointA (m := m) 1 4 - terminalVertex (m := m) 1
        = (((1 : ZMod m), (3 : ZMod m)) : TerminalQ m) from by
      simp only [terminalEndpointA, terminalVertex, a1, q, Prod.mk_sub_mk]
      exact pair_eq (by ring) (by ring)]
    rw [omega_13 hm,
      show terminalVertex (m := m)
          (terminalRowEquiv TerminalRow.chiMinus 1)
          = ((1 : ZMod m), (0 : ZMod m)) from rfl]
    rw [Prod.mk_add_mk]
    exact pair_eq (by ring) (by ring)
  simp only [terminalCompressedEndpointReturn]
  rw [heta, terminalExchange_one, ex1_23 hm]
  rfl

private theorem b1_Ep {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    terminalCompressedEndpointReturn (m := m) terminalExchange 1
        (terminalEndpointEplus (m := m) 1) =
      terminalEndpointB (m := m) 1 2 := by
  have heta : terminalEta (m := m) 1 (terminalEndpointEplus (m := m) 1)
      = terminalEndpointA (m := m) 1 2 := by
    simp only [terminalEta]
    rw [show terminalEndpointEplus (m := m) 1 - terminalVertex (m := m) 1
        = (((0 : ZMod m), (2 : ZMod m)) : TerminalQ m) from by
      simp only [terminalEndpointEplus, terminalVertex, a1, q,
        Prod.mk_sub_mk]
      exact pair_eq (by ring) (by ring)]
    rw [omega_02 hm,
      show terminalVertex (m := m)
          (terminalRowEquiv TerminalRow.chiMinus 1)
          = ((1 : ZMod m), (0 : ZMod m)) from rfl]
    rw [Prod.mk_add_mk]
    simp only [terminalEndpointA]
    exact pair_eq (by ring) (by ring)
  simp only [terminalCompressedEndpointReturn]
  rw [heta]
  exact terminalExchange_endpointA hm 1 2

private theorem b1_B4 {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    terminalCompressedEndpointReturn (m := m) terminalExchange 1
        (terminalEndpointB (m := m) 1 4) =
      terminalEndpointEminus (m := m) 1 := by
  have heta : terminalEta (m := m) 1 (terminalEndpointB (m := m) 1 4)
      = (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m) := by
    simp only [terminalEta]
    rw [show terminalEndpointB (m := m) 1 4 - terminalVertex (m := m) 1
        = (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m) from by
      simp only [terminalEndpointB, terminalVertex, a1, q, Prod.mk_sub_mk]
      exact pair_eq (by ring) (by ring)]
    rw [omega_03 hm,
      show terminalVertex (m := m)
          (terminalRowEquiv TerminalRow.chiPlus 1)
          = ((0 : ZMod m), (0 : ZMod m)) from rfl]
    rw [Prod.mk_add_mk]
    exact pair_eq (by ring) (by ring)
  simp only [terminalCompressedEndpointReturn]
  rw [heta, terminalExchange_one, ex1_03]
  rfl

private theorem b1_Em {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    terminalCompressedEndpointReturn (m := m) terminalExchange 1
        (terminalEndpointEminus (m := m) 1) =
      terminalEndpointA (m := m) 1 2 := by
  have heta : terminalEta (m := m) 1 (terminalEndpointEminus (m := m) 1)
      = terminalEndpointB (m := m) 1 2 := by
    simp only [terminalEta]
    rw [show terminalEndpointEminus (m := m) 1 - terminalVertex (m := m) 1
        = (((2 : ZMod m), (2 : ZMod m)) : TerminalQ m) from by
      simp only [terminalEndpointEminus, terminalVertex, a1, q,
        Prod.mk_sub_mk]
      exact pair_eq (by ring) (by ring)]
    rw [omega_22 hm,
      show terminalVertex (m := m)
          (terminalRowEquiv TerminalRow.chiPlus 1)
          = ((0 : ZMod m), (0 : ZMod m)) from rfl]
    rw [Prod.mk_add_mk]
    simp only [terminalEndpointB]
    exact pair_eq (by ring) (by ring)
  simp only [terminalCompressedEndpointReturn]
  rw [heta]
  exact terminalExchange_endpointB hm 1 2

private theorem b2_A2 {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    terminalCompressedEndpointReturn (m := m) terminalExchange 2
        (terminalEndpointA (m := m) 2 2) =
      terminalEndpointEminus (m := m) 2 := by
  have heta : terminalEta (m := m) 2 (terminalEndpointA (m := m) 2 2)
      = (((2 : ZMod m), (1 : ZMod m)) : TerminalQ m) := by
    simp only [terminalEta]
    rw [show terminalEndpointA (m := m) 2 2 - terminalVertex (m := m) 2
        = (((1 : ZMod m), (1 : ZMod m)) : TerminalQ m) from by
      simp only [terminalEndpointA, terminalVertex, a2, q, Prod.mk_sub_mk]
      exact pair_eq (by ring) (by ring)]
    rw [omega_11 hm,
      show terminalVertex (m := m)
          (terminalRowEquiv TerminalRow.chiPlus 2)
          = ((1 : ZMod m), (0 : ZMod m)) from rfl]
    rw [Prod.mk_add_mk]
    exact pair_eq (by ring) (by ring)
  simp only [terminalCompressedEndpointReturn]
  rw [heta, terminalExchange_two, ex2_21]
  rfl

private theorem b2_Em {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    terminalCompressedEndpointReturn (m := m) terminalExchange 2
        (terminalEndpointEminus (m := m) 2) =
      terminalEndpointB (m := m) 2 4 := by
  have heta : terminalEta (m := m) 2 (terminalEndpointEminus (m := m) 2)
      = terminalEndpointA (m := m) 2 4 := by
    simp only [terminalEta]
    rw [show terminalEndpointEminus (m := m) 2 - terminalVertex (m := m) 2
        = (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m) from by
      simp only [terminalEndpointEminus, terminalVertex, a2, q,
        Prod.mk_sub_mk]
      exact pair_eq (by ring) (by ring)]
    rw [omega_03 hm,
      show terminalVertex (m := m)
          (terminalRowEquiv TerminalRow.chiPlus 2)
          = ((1 : ZMod m), (0 : ZMod m)) from rfl]
    rw [Prod.mk_add_mk]
    simp only [terminalEndpointA]
    exact pair_eq (by ring) (by ring)
  simp only [terminalCompressedEndpointReturn]
  rw [heta]
  exact terminalExchange_endpointA hm 2 4

private theorem b2_B2 {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    terminalCompressedEndpointReturn (m := m) terminalExchange 2
        (terminalEndpointB (m := m) 2 2) =
      terminalEndpointEplus (m := m) 2 := by
  have heta : terminalEta (m := m) 2 (terminalEndpointB (m := m) 2 2)
      = (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m) := by
    simp only [terminalEta]
    rw [show terminalEndpointB (m := m) 2 2 - terminalVertex (m := m) 2
        = (((0 : ZMod m), (2 : ZMod m)) : TerminalQ m) from by
      simp only [terminalEndpointB, terminalVertex, a2, q, Prod.mk_sub_mk]
      exact pair_eq (by ring) (by ring)]
    rw [omega_02 hm,
      show terminalVertex (m := m)
          (terminalRowEquiv TerminalRow.chiMinus 2)
          = ((0 : ZMod m), (1 : ZMod m)) from rfl]
    rw [Prod.mk_add_mk]
    exact pair_eq (by ring) (by ring)
  simp only [terminalCompressedEndpointReturn]
  rw [heta, terminalExchange_two, ex2_03 hm]
  rfl

private theorem b2_Ep {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    terminalCompressedEndpointReturn (m := m) terminalExchange 2
        (terminalEndpointEplus (m := m) 2) =
      terminalEndpointA (m := m) 2 4 := by
  have heta : terminalEta (m := m) 2 (terminalEndpointEplus (m := m) 2)
      = (((2 : ZMod m), (2 : ZMod m)) : TerminalQ m) := by
    simp only [terminalEta]
    rw [show terminalEndpointEplus (m := m) 2 - terminalVertex (m := m) 2
        = (((2 : ZMod m), (1 : ZMod m)) : TerminalQ m) from by
      simp only [terminalEndpointEplus, terminalVertex, a2, q,
        Prod.mk_sub_mk]
      exact pair_eq (by ring) (by ring)]
    rw [omega_21 hm,
      show terminalVertex (m := m)
          (terminalRowEquiv TerminalRow.chiMinus 2)
          = ((0 : ZMod m), (1 : ZMod m)) from rfl]
    rw [Prod.mk_add_mk]
    exact pair_eq (by ring) (by ring)
  simp only [terminalCompressedEndpointReturn]
  rw [heta, terminalExchange_two, ex2_22 hm,
    show terminalEndpointA (m := m) 2 4
        = (((1 : ZMod m), (3 : ZMod m)) : TerminalQ m) from by
      simp only [terminalEndpointA]
      exact pair_eq rfl (by ring)]

/-! ## The recurrence instance -/

/-- The first concrete instance of the paper's terminal `A₂` endpoint
recurrence: the per-fiber exchange `terminalExchange` satisfies all sixteen
recurrence fields for every modulus `m ≥ 6` (evenness is not required). -/
def terminalA2EndpointRecurrence (m : Nat) [NeZero m] (hm : 6 ≤ m) :
    D3TerminalA2Parametric.TerminalA2EndpointRecurrence m where
  exchange := terminalExchange
  exchange_A := terminalExchange_endpointA hm
  exchange_B := terminalExchange_endpointB hm
  generic_A := by
    intro c r hexc
    fin_cases c
    · exact genA0 hm (fun h => hexc (Or.inl h)) (fun h => hexc (Or.inr h))
    · exact genA1 hm (fun h => hexc (Or.inl h)) (fun h => hexc (Or.inr h))
    · exact genA2 hm (fun h => hexc (Or.inl h)) (fun h => hexc (Or.inr h))
  generic_B := by
    intro c r hexc
    fin_cases c
    · exact genB0 hm (fun h => hexc (Or.inl h)) (fun h => hexc (Or.inr h))
    · exact genB1 hm (fun h => hexc (Or.inl h)) (fun h => hexc (Or.inr h))
    · exact genB2 hm (fun h => hexc (Or.inl h)) (fun h => hexc (Or.inr h))
  boundary0_B3 := b0_B3 hm
  boundary0_Eplus := b0_Ep hm
  boundary0_A3 := b0_A3 hm
  boundary0_Eminus := b0_Em hm
  boundary1_A4 := b1_A4 hm
  boundary1_Eplus := b1_Ep hm
  boundary1_B4 := b1_B4 hm
  boundary1_Eminus := b1_Em hm
  boundary2_A2 := b2_A2 hm
  boundary2_Eminus := b2_Em hm
  boundary2_B2 := b2_B2 hm
  boundary2_Eplus := b2_Ep hm

/-! ## H1a endpoint-cycle conclusion for the concrete instance -/

/-- H1a endpoint-cycle target for the concrete exchange: for every even
`m ≥ 6`, the compressed endpoint return built from `terminalExchange` is a
single cycle on each active endpoint image. -/
theorem terminalEndpointImage_singleCycle {m : Nat} [NeZero m]
    (hmEven : Even m) (hm : 6 ≤ m) (c : TorusColor 3) :
    Shared.IsSingleCycleMap
      (TerminalA2EndpointRank.endpointImageMapOfRankStep c
        (D3TerminalA2Parametric.terminalCompressedEndpointReturn
          (m := m) (terminalA2EndpointRecurrence m hm).exchange c)
        (TerminalA2EndpointRank.compressedEndpoint_rank_step_of_desc_rank_step
          hm (terminalA2EndpointRecurrence m hm) c
          (TerminalA2EndpointRank.endpointDesc_rank_step hmEven hm c))) :=
  TerminalA2EndpointRank.compressedEndpointImageMap_singleCycle_of_recurrence
    hmEven hm (terminalA2EndpointRecurrence m hm) c

end TerminalA2RecurrenceInstance
end V28Hard
end EvenV11
