import EvenV11.V28Hard.TerminalA2RecurrenceInstance

/-!
# Terminal `A₂` active-set identification (H1a)

This file characterizes, per terminal color `c` and for every modulus
`m ≥ 6`, exactly where the paper jump `η_c` moves a point: the predicate
`activePred c z` holds iff `terminalEta c z ≠ z`.

The active set of each color is the union of two affine lines (with one
collision point removed) and two extra puncture points; it coincides with
the closed-form endpoint family `A_i(r)`, `B_i(r)` (for `r` away from the
collision index) together with `E⁺_i` and `E⁻_i` from
`D3TerminalA2Parametric`.  On each fiber of the label `ℓ_i` the active
points are exactly a distinguished pair: `A_i(g), B_i(g)` on generic
fibers and `E⁺_i, E⁻_i` on the collision fiber.  These are the facts the
interval-splice step of the terminal `A₂` argument consumes.
-/

namespace EvenV11
namespace V28Hard
namespace TerminalA2ActiveSet

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

private theorem pair_ne_left {m : Nat} {x y a b : ZMod m} (h : x ≠ a) :
    ((x, y) : TerminalQ m) ≠ (a, b) :=
  fun he => h (congrArg Prod.fst he)

private theorem pair_ne_right {m : Nat} {x y a b : ZMod m} (h : y ≠ b) :
    ((x, y) : TerminalQ m) ≠ (a, b) :=
  fun he => h (congrArg Prod.snd he)

private theorem pair_ne_sum {m : Nat} {x y a b : ZMod m}
    (h : x + y ≠ a + b) : ((x, y) : TerminalQ m) ≠ (a, b) := by
  intro he
  rw [Prod.mk.injEq] at he
  exact h (by rw [he.1, he.2])

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

private theorem omega_12 {m : Nat} [NeZero m] :
    terminalOmega (((1 : ZMod m), (2 : ZMod m)) : TerminalQ m)
      = TerminalRow.default := by
  simp only [terminalOmega]
  rw [if_pos (pPt (m := m)).symm]

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

private theorem omega_default {m : Nat} [NeZero m] {w : TerminalQ m}
    (h1 : w ≠ ((1 : ZMod m), (2 : ZMod m)))
    (h2 : w ≠ ((0 : ZMod m), (2 : ZMod m)))
    (h3 : w ≠ ((2 : ZMod m), (2 : ZMod m)))
    (h4 : w ≠ ((1 : ZMod m), (1 : ZMod m)))
    (h5 : w ≠ ((1 : ZMod m), (3 : ZMod m)))
    (h6 : w ≠ ((2 : ZMod m), (1 : ZMod m)))
    (h7 : w ≠ ((0 : ZMod m), (3 : ZMod m)))
    (h8 : w.2 ≠ (2 : ZMod m))
    (h9 : w.1 ≠ (1 : ZMod m))
    (h10 : w.1 + w.2 ≠ (3 : ZMod m)) :
    terminalOmega w = TerminalRow.default := by
  have g1 : w ≠ p := by rw [pPt]; exact h1
  have g2 : w ≠ p - eH := by rw [pSubEH]; exact h2
  have g3 : w ≠ p + eH := by rw [pAddEH]; exact h3
  have g4 : w ≠ p - eV := by rw [pSubEV]; exact h4
  have g5 : w ≠ p + eV := by rw [pAddEV]; exact h5
  have g6 : w ≠ p - eD := by rw [pSubED]; exact h6
  have g7 : w ≠ p + eD := by rw [pAddED]; exact h7
  simp only [terminalOmega]
  rw [if_neg g1, if_neg g2, if_neg g3, if_neg g4, if_neg g5, if_neg g6,
    if_neg g7, if_neg h8, if_neg h9, if_neg h10]

/-! ## Fixed-point criterion for `terminalEta` -/

private theorem vertexInj {m : Nat} [NeZero m] (hm : 6 ≤ m)
    {i j : Fin 3}
    (h : terminalVertex (m := m) i = terminalVertex (m := m) j) :
    i = j := by
  have h01 : (0 : ZMod m) ≠ 1 := zNe01 hm
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | exact absurd (congrArg Prod.fst h) h01
      | exact absurd (congrArg Prod.fst h) h01.symm
      | exact absurd (congrArg Prod.snd h) h01
      | exact absurd (congrArg Prod.snd h) h01.symm

private theorem eta_fixed_iff {m : Nat} [NeZero m] (hm : 6 ≤ m)
    (c : TorusColor 3) (z : TerminalQ m) :
    terminalEta (m := m) c z = z ↔
      terminalRowEquiv (terminalOmega (z - terminalVertex (m := m) c)) c
        = c := by
  constructor
  · intro h
    simp only [terminalEta] at h
    refine vertexInj hm ?_
    have h2 :
        terminalVertex (m := m)
            (terminalRowEquiv
              (terminalOmega (z - terminalVertex (m := m) c)) c) =
          z - (z - terminalVertex (m := m) c) :=
      eq_sub_of_add_eq (by rw [add_comm]; exact h)
    rw [h2, sub_sub_cancel]
  · intro h
    simp only [terminalEta]
    rw [h, sub_add_cancel]

private theorem sub_vertex0 {m : Nat} [NeZero m] (z : TerminalQ m) :
    z - terminalVertex (m := m) 0 = (z.1 - 1, z.2) := by
  have hv : terminalVertex (m := m) 0 = ((1 : ZMod m), (0 : ZMod m)) := rfl
  rw [hv]
  refine Prod.ext ?_ ?_ <;> simp

private theorem sub_vertex1 {m : Nat} [NeZero m] (z : TerminalQ m) :
    z - terminalVertex (m := m) 1 = (z.1, z.2 - 1) := by
  have hv : terminalVertex (m := m) 1 = ((0 : ZMod m), (1 : ZMod m)) := rfl
  rw [hv]
  refine Prod.ext ?_ ?_ <;> simp

private theorem sub_vertex2 {m : Nat} [NeZero m] (z : TerminalQ m) :
    z - terminalVertex (m := m) 2 = (z.1, z.2) := by
  have hv : terminalVertex (m := m) 2 = ((0 : ZMod m), (0 : ZMod m)) := rfl
  rw [hv]
  refine Prod.ext ?_ ?_ <;> simp

/-! ## The active predicate -/

/-- Active set of the terminal jump `η_c`: for `m ≥ 6`, `activePred c z`
holds iff `terminalEta c z ≠ z`.  Per color it is the union of two affine
lines (minus their intersection with the collision fiber) and two extra
puncture points. -/
def activePred {m : Nat} [NeZero m] : TorusColor 3 → TerminalQ m → Prop
  | 0, z => (z.2 = 2 ∧ z.1 ≠ 2) ∨ (z.1 + z.2 = 4 ∧ z.1 ≠ 2) ∨
      z = ((2 : ZMod m), (1 : ZMod m)) ∨ z = ((2 : ZMod m), (3 : ZMod m))
  | 1, z => (z.1 = 1 ∧ z.2 ≠ 3) ∨ (z.1 + z.2 = 4 ∧ z.2 ≠ 3) ∨
      z = ((0 : ZMod m), (3 : ZMod m)) ∨ z = ((2 : ZMod m), (3 : ZMod m))
  | _, z => (z.2 = 2 ∧ z.1 ≠ 1) ∨ (z.1 = 1 ∧ z.2 ≠ 2) ∨
      z = ((2 : ZMod m), (1 : ZMod m)) ∨ z = ((0 : ZMod m), (3 : ZMod m))

/-! ## Inactivity: `η_c` fixes every non-active point -/

private theorem inactive0 {m : Nat} [NeZero m] (hm : 6 ≤ m)
    (z : TerminalQ m)
    (hA : ¬(z.2 = 2 ∧ z.1 ≠ 2)) (hB : ¬(z.1 + z.2 = 4 ∧ z.1 ≠ 2))
    (hC : z ≠ ((2 : ZMod m), (1 : ZMod m)))
    (hD : z ≠ ((2 : ZMod m), (3 : ZMod m))) :
    terminalEta (m := m) 0 z = z := by
  apply (eta_fixed_iff hm 0 z).mpr
  rw [sub_vertex0 z]
  by_cases hy : z.2 = 2
  · have hx : z.1 = 2 := by
      by_contra hx
      exact hA ⟨hy, hx⟩
    rw [show ((z.1 - 1, z.2) : TerminalQ m)
        = ((1 : ZMod m), (2 : ZMod m)) from
      pair_eq (by rw [hx]; ring) hy]
    rw [omega_12]
    decide
  · by_cases hx : z.1 = 2
    · have hw1 : z.1 - 1 = (1 : ZMod m) := by rw [hx]; ring
      have hy1 : z.2 ≠ 1 := fun h => hC (pair_eq hx h)
      have hy3 : z.2 ≠ 3 := fun h => hD (pair_eq hx h)
      rw [omega_tau12 (w := ((z.1 - 1, z.2) : TerminalQ m))
        (pair_ne_right hy) (pair_ne_right hy) (pair_ne_right hy)
        (pair_ne_right hy1) (pair_ne_right hy3)
        (pair_ne_left (by rw [hw1]; exact zNe12 hm))
        (pair_ne_left (by rw [hw1]; exact (zNe01 hm).symm))
        hy hw1]
      decide
    · by_cases hs : z.1 + z.2 = 4
      · exact absurd ⟨hs, hx⟩ hB
      · rw [omega_default (w := ((z.1 - 1, z.2) : TerminalQ m))
          (pair_ne_right hy) (pair_ne_right hy) (pair_ne_right hy)
          (pair_ne_left fun h => hx (by linear_combination h))
          (pair_ne_left fun h => hx (by linear_combination h))
          (pair_ne_sum fun h => hs (by linear_combination h))
          (pair_ne_sum fun h => hs (by linear_combination h))
          hy (fun h => hx (by linear_combination h))
          (fun h => hs (by linear_combination h))]
        decide

private theorem inactive1 {m : Nat} [NeZero m] (hm : 6 ≤ m)
    (z : TerminalQ m)
    (hA : ¬(z.1 = 1 ∧ z.2 ≠ 3)) (hB : ¬(z.1 + z.2 = 4 ∧ z.2 ≠ 3))
    (hC : z ≠ ((0 : ZMod m), (3 : ZMod m)))
    (hD : z ≠ ((2 : ZMod m), (3 : ZMod m))) :
    terminalEta (m := m) 1 z = z := by
  apply (eta_fixed_iff hm 1 z).mpr
  rw [sub_vertex1 z]
  by_cases hy : z.2 = 3
  · have hw2 : z.2 - 1 = (2 : ZMod m) := by rw [hy]; ring
    have hx0 : z.1 ≠ 0 := fun h => hC (pair_eq h hy)
    have hx2 : z.1 ≠ 2 := fun h => hD (pair_eq h hy)
    by_cases hx1 : z.1 = 1
    · rw [show ((z.1, z.2 - 1) : TerminalQ m)
          = ((1 : ZMod m), (2 : ZMod m)) from pair_eq hx1 hw2]
      rw [omega_12]
      decide
    · rw [omega_tau02 (w := ((z.1, z.2 - 1) : TerminalQ m))
        (pair_ne_left hx1) (pair_ne_left hx0) (pair_ne_left hx2)
        (pair_ne_left hx1) (pair_ne_left hx1) (pair_ne_left hx2)
        (pair_ne_left hx0) hw2]
      decide
  · have hx : z.1 ≠ 1 := fun h => hA ⟨h, hy⟩
    have hs : z.1 + z.2 ≠ 4 := fun h => hB ⟨h, hy⟩
    rw [omega_default (w := ((z.1, z.2 - 1) : TerminalQ m))
      (pair_ne_left hx)
      (pair_ne_right fun h => hy (by linear_combination h))
      (pair_ne_right fun h => hy (by linear_combination h))
      (pair_ne_left hx) (pair_ne_left hx)
      (pair_ne_sum fun h => hs (by linear_combination h))
      (pair_ne_sum fun h => hs (by linear_combination h))
      (fun h => hy (by linear_combination h)) hx
      (fun h => hs (by linear_combination h))]
    decide

private theorem inactive2 {m : Nat} [NeZero m] (hm : 6 ≤ m)
    (z : TerminalQ m)
    (hA : ¬(z.2 = 2 ∧ z.1 ≠ 1)) (hB : ¬(z.1 = 1 ∧ z.2 ≠ 2))
    (hC : z ≠ ((2 : ZMod m), (1 : ZMod m)))
    (hD : z ≠ ((0 : ZMod m), (3 : ZMod m))) :
    terminalEta (m := m) 2 z = z := by
  apply (eta_fixed_iff hm 2 z).mpr
  rw [sub_vertex2 z]
  by_cases hy : z.2 = 2
  · have hx : z.1 = 1 := by
      by_contra hx
      exact hA ⟨hy, hx⟩
    rw [show ((z.1, z.2) : TerminalQ m)
        = ((1 : ZMod m), (2 : ZMod m)) from pair_eq hx hy]
    rw [omega_12]
    decide
  · have hx : z.1 ≠ 1 := fun h => hB ⟨h, hy⟩
    by_cases hs : z.1 + z.2 = 3
    · rw [omega_tau01 (w := ((z.1, z.2) : TerminalQ m))
        (pair_ne_left hx) (pair_ne_right hy) (pair_ne_right hy)
        (pair_ne_left hx) (pair_ne_left hx) hC hD hy hx hs]
      decide
    · rw [omega_default (w := ((z.1, z.2) : TerminalQ m))
        (pair_ne_left hx) (pair_ne_right hy) (pair_ne_right hy)
        (pair_ne_left hx) (pair_ne_left hx) hC hD hy hx hs]
      decide

/-- H1a inactivity: away from the active set, the terminal jump `η_c` is
the identity.  This is the crucial direction for the interval splice. -/
theorem terminalEta_eq_self_of_not_active {m : Nat} [NeZero m] (hm : 6 ≤ m)
    (c : TorusColor 3) (z : TerminalQ m) (hz : ¬ activePred c z) :
    TerminalA2LowMod.terminalEta c z = z := by
  fin_cases c
  · exact inactive0 hm z (fun h => hz (Or.inl h))
      (fun h => hz (Or.inr (Or.inl h)))
      (fun h => hz (Or.inr (Or.inr (Or.inl h))))
      (fun h => hz (Or.inr (Or.inr (Or.inr h))))
  · exact inactive1 hm z (fun h => hz (Or.inl h))
      (fun h => hz (Or.inr (Or.inl h)))
      (fun h => hz (Or.inr (Or.inr (Or.inl h))))
      (fun h => hz (Or.inr (Or.inr (Or.inr h))))
  · exact inactive2 hm z (fun h => hz (Or.inl h))
      (fun h => hz (Or.inr (Or.inl h)))
      (fun h => hz (Or.inr (Or.inr (Or.inl h))))
      (fun h => hz (Or.inr (Or.inr (Or.inr h))))

/-! ## Activity: `η_c` moves every active point -/

private theorem active0 {m : Nat} [NeZero m] (hm : 6 ≤ m)
    (z : TerminalQ m)
    (hz : (z.2 = 2 ∧ z.1 ≠ 2) ∨ (z.1 + z.2 = 4 ∧ z.1 ≠ 2) ∨
      z = ((2 : ZMod m), (1 : ZMod m)) ∨
      z = ((2 : ZMod m), (3 : ZMod m))) :
    terminalEta (m := m) 0 z ≠ z := by
  intro hfix
  have hrow := (eta_fixed_iff hm 0 z).mp hfix
  rw [sub_vertex0 z] at hrow
  rcases hz with ⟨hy, hx⟩ | ⟨hs, hx⟩ | hz | hz
  · by_cases hx1 : z.1 = 1
    · rw [show ((z.1 - 1, z.2) : TerminalQ m)
          = ((0 : ZMod m), (2 : ZMod m)) from
        pair_eq (by rw [hx1]; ring) hy, omega_02 hm] at hrow
      exact absurd hrow (by decide)
    · by_cases hx3 : z.1 = 3
      · rw [show ((z.1 - 1, z.2) : TerminalQ m)
            = ((2 : ZMod m), (2 : ZMod m)) from
          pair_eq (by rw [hx3]; ring) hy, omega_22 hm] at hrow
        exact absurd hrow (by decide)
      · rw [omega_tau02 (w := ((z.1 - 1, z.2) : TerminalQ m))
          (pair_ne_left fun h => hx (by linear_combination h))
          (pair_ne_left fun h => hx1 (by linear_combination h))
          (pair_ne_left fun h => hx3 (by linear_combination h))
          (pair_ne_right (by rw [hy]; exact (zNe12 hm).symm))
          (pair_ne_right (by rw [hy]; exact zNe23 hm))
          (pair_ne_right (by rw [hy]; exact (zNe12 hm).symm))
          (pair_ne_right (by rw [hy]; exact zNe23 hm))
          hy] at hrow
        exact absurd hrow (by decide)
  · have hy : z.2 ≠ 2 := fun h => hx (by linear_combination hs - h)
    by_cases hx3 : z.1 = 3
    · have hy1 : z.2 = 1 := by linear_combination hs - hx3
      rw [show ((z.1 - 1, z.2) : TerminalQ m)
          = ((2 : ZMod m), (1 : ZMod m)) from
        pair_eq (by rw [hx3]; ring) hy1, omega_21 hm] at hrow
      exact absurd hrow (by decide)
    · by_cases hx1 : z.1 = 1
      · have hy3 : z.2 = 3 := by linear_combination hs - hx1
        rw [show ((z.1 - 1, z.2) : TerminalQ m)
            = ((0 : ZMod m), (3 : ZMod m)) from
          pair_eq (by rw [hx1]; ring) hy3, omega_03 hm] at hrow
        exact absurd hrow (by decide)
      · rw [omega_tau01 (w := ((z.1 - 1, z.2) : TerminalQ m))
          (pair_ne_right hy) (pair_ne_right hy) (pair_ne_right hy)
          (pair_ne_left fun h => hx (by linear_combination h))
          (pair_ne_left fun h => hx (by linear_combination h))
          (pair_ne_left fun h => hx3 (by linear_combination h))
          (pair_ne_left fun h => hx1 (by linear_combination h))
          hy (fun h => hx (by linear_combination h))
          (by linear_combination hs)] at hrow
        exact absurd hrow (by decide)
  · have hx2 : z.1 = 2 := by rw [hz]
    have hy1 : z.2 = 1 := by rw [hz]
    rw [show ((z.1 - 1, z.2) : TerminalQ m)
        = ((1 : ZMod m), (1 : ZMod m)) from
      pair_eq (by rw [hx2]; ring) hy1, omega_11 hm] at hrow
    exact absurd hrow (by decide)
  · have hx2 : z.1 = 2 := by rw [hz]
    have hy3 : z.2 = 3 := by rw [hz]
    rw [show ((z.1 - 1, z.2) : TerminalQ m)
        = ((1 : ZMod m), (3 : ZMod m)) from
      pair_eq (by rw [hx2]; ring) hy3, omega_13 hm] at hrow
    exact absurd hrow (by decide)

private theorem active1 {m : Nat} [NeZero m] (hm : 6 ≤ m)
    (z : TerminalQ m)
    (hz : (z.1 = 1 ∧ z.2 ≠ 3) ∨ (z.1 + z.2 = 4 ∧ z.2 ≠ 3) ∨
      z = ((0 : ZMod m), (3 : ZMod m)) ∨
      z = ((2 : ZMod m), (3 : ZMod m))) :
    terminalEta (m := m) 1 z ≠ z := by
  intro hfix
  have hrow := (eta_fixed_iff hm 1 z).mp hfix
  rw [sub_vertex1 z] at hrow
  rcases hz with ⟨hx, hy⟩ | ⟨hs, hy⟩ | hz | hz
  · by_cases hy2 : z.2 = 2
    · rw [show ((z.1, z.2 - 1) : TerminalQ m)
          = ((1 : ZMod m), (1 : ZMod m)) from
        pair_eq hx (by rw [hy2]; ring), omega_11 hm] at hrow
      exact absurd hrow (by decide)
    · by_cases hy4 : z.2 = 4
      · rw [show ((z.1, z.2 - 1) : TerminalQ m)
            = ((1 : ZMod m), (3 : ZMod m)) from
          pair_eq hx (by rw [hy4]; ring), omega_13 hm] at hrow
        exact absurd hrow (by decide)
      · rw [omega_tau12 (w := ((z.1, z.2 - 1) : TerminalQ m))
          (pair_ne_right fun h => hy (by linear_combination h))
          (pair_ne_left (by rw [hx]; exact (zNe01 hm).symm))
          (pair_ne_left (by rw [hx]; exact zNe12 hm))
          (pair_ne_right fun h => hy2 (by linear_combination h))
          (pair_ne_right fun h => hy4 (by linear_combination h))
          (pair_ne_left (by rw [hx]; exact zNe12 hm))
          (pair_ne_left (by rw [hx]; exact (zNe01 hm).symm))
          (fun h => hy (by linear_combination h)) hx] at hrow
        exact absurd hrow (by decide)
  · have hx1 : z.1 ≠ 1 := fun h => hy (by linear_combination hs - h)
    by_cases hy2 : z.2 = 2
    · have hx2 : z.1 = 2 := by linear_combination hs - hy2
      rw [show ((z.1, z.2 - 1) : TerminalQ m)
          = ((2 : ZMod m), (1 : ZMod m)) from
        pair_eq hx2 (by rw [hy2]; ring), omega_21 hm] at hrow
      exact absurd hrow (by decide)
    · by_cases hy4 : z.2 = 4
      · have hx0 : z.1 = 0 := by linear_combination hs - hy4
        rw [show ((z.1, z.2 - 1) : TerminalQ m)
            = ((0 : ZMod m), (3 : ZMod m)) from
          pair_eq hx0 (by rw [hy4]; ring), omega_03 hm] at hrow
        exact absurd hrow (by decide)
      · rw [omega_tau01 (w := ((z.1, z.2 - 1) : TerminalQ m))
          (pair_ne_left hx1)
          (pair_ne_right fun h => hy (by linear_combination h))
          (pair_ne_right fun h => hy (by linear_combination h))
          (pair_ne_left hx1) (pair_ne_left hx1)
          (pair_ne_left fun h => hy2 (by linear_combination hs - h))
          (pair_ne_left fun h => hy4 (by linear_combination hs - h))
          (fun h => hy (by linear_combination h)) hx1
          (by linear_combination hs)] at hrow
        exact absurd hrow (by decide)
  · have hx0 : z.1 = 0 := by rw [hz]
    have hy3 : z.2 = 3 := by rw [hz]
    rw [show ((z.1, z.2 - 1) : TerminalQ m)
        = ((0 : ZMod m), (2 : ZMod m)) from
      pair_eq hx0 (by rw [hy3]; ring), omega_02 hm] at hrow
    exact absurd hrow (by decide)
  · have hx2 : z.1 = 2 := by rw [hz]
    have hy3 : z.2 = 3 := by rw [hz]
    rw [show ((z.1, z.2 - 1) : TerminalQ m)
        = ((2 : ZMod m), (2 : ZMod m)) from
      pair_eq hx2 (by rw [hy3]; ring), omega_22 hm] at hrow
    exact absurd hrow (by decide)

private theorem active2 {m : Nat} [NeZero m] (hm : 6 ≤ m)
    (z : TerminalQ m)
    (hz : (z.2 = 2 ∧ z.1 ≠ 1) ∨ (z.1 = 1 ∧ z.2 ≠ 2) ∨
      z = ((2 : ZMod m), (1 : ZMod m)) ∨
      z = ((0 : ZMod m), (3 : ZMod m))) :
    terminalEta (m := m) 2 z ≠ z := by
  intro hfix
  have hrow := (eta_fixed_iff hm 2 z).mp hfix
  rw [sub_vertex2 z] at hrow
  rcases hz with ⟨hy, hx⟩ | ⟨hx, hy⟩ | hz | hz
  · by_cases hx0 : z.1 = 0
    · rw [show ((z.1, z.2) : TerminalQ m)
          = ((0 : ZMod m), (2 : ZMod m)) from
        pair_eq hx0 hy, omega_02 hm] at hrow
      exact absurd hrow (by decide)
    · by_cases hx2 : z.1 = 2
      · rw [show ((z.1, z.2) : TerminalQ m)
            = ((2 : ZMod m), (2 : ZMod m)) from
          pair_eq hx2 hy, omega_22 hm] at hrow
        exact absurd hrow (by decide)
      · rw [omega_tau02 (w := ((z.1, z.2) : TerminalQ m))
          (pair_ne_left hx) (pair_ne_left hx0) (pair_ne_left hx2)
          (pair_ne_right (by rw [hy]; exact (zNe12 hm).symm))
          (pair_ne_right (by rw [hy]; exact zNe23 hm))
          (pair_ne_right (by rw [hy]; exact (zNe12 hm).symm))
          (pair_ne_right (by rw [hy]; exact zNe23 hm))
          hy] at hrow
        exact absurd hrow (by decide)
  · by_cases hy1 : z.2 = 1
    · rw [show ((z.1, z.2) : TerminalQ m)
          = ((1 : ZMod m), (1 : ZMod m)) from
        pair_eq hx hy1, omega_11 hm] at hrow
      exact absurd hrow (by decide)
    · by_cases hy3 : z.2 = 3
      · rw [show ((z.1, z.2) : TerminalQ m)
            = ((1 : ZMod m), (3 : ZMod m)) from
          pair_eq hx hy3, omega_13 hm] at hrow
        exact absurd hrow (by decide)
      · rw [omega_tau12 (w := ((z.1, z.2) : TerminalQ m))
          (pair_ne_right hy)
          (pair_ne_left (by rw [hx]; exact (zNe01 hm).symm))
          (pair_ne_left (by rw [hx]; exact zNe12 hm))
          (pair_ne_right hy1) (pair_ne_right hy3)
          (pair_ne_left (by rw [hx]; exact zNe12 hm))
          (pair_ne_left (by rw [hx]; exact (zNe01 hm).symm))
          hy hx] at hrow
        exact absurd hrow (by decide)
  · have hx2 : z.1 = 2 := by rw [hz]
    have hy1 : z.2 = 1 := by rw [hz]
    rw [show ((z.1, z.2) : TerminalQ m)
        = ((2 : ZMod m), (1 : ZMod m)) from
      pair_eq hx2 hy1, omega_21 hm] at hrow
    exact absurd hrow (by decide)
  · have hx0 : z.1 = 0 := by rw [hz]
    have hy3 : z.2 = 3 := by rw [hz]
    rw [show ((z.1, z.2) : TerminalQ m)
        = ((0 : ZMod m), (3 : ZMod m)) from
      pair_eq hx0 hy3, omega_03 hm] at hrow
    exact absurd hrow (by decide)

/-- H1a activity: on the active set, the terminal jump `η_c` moves every
point. -/
theorem terminalEta_ne_self_of_active {m : Nat} [NeZero m] (hm : 6 ≤ m)
    (c : TorusColor 3) (z : TerminalQ m) (hz : activePred c z) :
    TerminalA2LowMod.terminalEta c z ≠ z := by
  fin_cases c
  · exact active0 hm z hz
  · exact active1 hm z hz
  · exact active2 hm z hz

/-! ## Endpoint-list correspondence -/

private theorem endpoint_iff0 {m : Nat} [NeZero m] (z : TerminalQ m) :
    (z.2 = 2 ∧ z.1 ≠ 2) ∨ (z.1 + z.2 = 4 ∧ z.1 ≠ 2) ∨
        z = ((2 : ZMod m), (1 : ZMod m)) ∨
        z = ((2 : ZMod m), (3 : ZMod m)) ↔
      (∃ r, r ≠ (2 : ZMod m) ∧ z = ((r, 2) : TerminalQ m)) ∨
        (∃ r, r ≠ (2 : ZMod m) ∧ z = ((r, 4 - r) : TerminalQ m)) ∨
        z = ((2 : ZMod m), (3 : ZMod m)) ∨
        z = ((2 : ZMod m), (1 : ZMod m)) := by
  constructor
  · rintro (⟨hy, hx⟩ | ⟨hs, hx⟩ | hz | hz)
    · exact Or.inl ⟨z.1, hx, pair_eq rfl hy⟩
    · exact Or.inr (Or.inl ⟨z.1, hx, pair_eq rfl (by linear_combination hs)⟩)
    · exact Or.inr (Or.inr (Or.inr hz))
    · exact Or.inr (Or.inr (Or.inl hz))
  · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | rfl | rfl)
    · exact Or.inl ⟨rfl, hr⟩
    · exact Or.inr (Or.inl ⟨show r + (4 - r) = (4 : ZMod m) by ring, hr⟩)
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl rfl))

private theorem endpoint_iff1 {m : Nat} [NeZero m] (z : TerminalQ m) :
    (z.1 = 1 ∧ z.2 ≠ 3) ∨ (z.1 + z.2 = 4 ∧ z.2 ≠ 3) ∨
        z = ((0 : ZMod m), (3 : ZMod m)) ∨
        z = ((2 : ZMod m), (3 : ZMod m)) ↔
      (∃ r, r ≠ (3 : ZMod m) ∧ z = ((1, r) : TerminalQ m)) ∨
        (∃ r, r ≠ (3 : ZMod m) ∧ z = ((4 - r, r) : TerminalQ m)) ∨
        z = ((0 : ZMod m), (3 : ZMod m)) ∨
        z = ((2 : ZMod m), (3 : ZMod m)) := by
  constructor
  · rintro (⟨hx, hy⟩ | ⟨hs, hy⟩ | hz | hz)
    · exact Or.inl ⟨z.2, hy, pair_eq hx rfl⟩
    · exact Or.inr (Or.inl ⟨z.2, hy, pair_eq (by linear_combination hs) rfl⟩)
    · exact Or.inr (Or.inr (Or.inl hz))
    · exact Or.inr (Or.inr (Or.inr hz))
  · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | rfl | rfl)
    · exact Or.inl ⟨rfl, hr⟩
    · exact Or.inr (Or.inl ⟨show (4 : ZMod m) - r + r = 4 by ring, hr⟩)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

private theorem endpoint_iff2 {m : Nat} [NeZero m] (z : TerminalQ m) :
    (z.2 = 2 ∧ z.1 ≠ 1) ∨ (z.1 = 1 ∧ z.2 ≠ 2) ∨
        z = ((2 : ZMod m), (1 : ZMod m)) ∨
        z = ((0 : ZMod m), (3 : ZMod m)) ↔
      (∃ r, r ≠ (3 : ZMod m) ∧ z = ((1, r - 1) : TerminalQ m)) ∨
        (∃ r, r ≠ (3 : ZMod m) ∧ z = ((r - 2, 2) : TerminalQ m)) ∨
        z = ((2 : ZMod m), (1 : ZMod m)) ∨
        z = ((0 : ZMod m), (3 : ZMod m)) := by
  constructor
  · rintro (⟨hy, hx⟩ | ⟨hx, hy⟩ | hz | hz)
    · exact Or.inr (Or.inl ⟨z.1 + 2, fun h => hx (by linear_combination h),
        pair_eq (by ring) hy⟩)
    · exact Or.inl ⟨z.2 + 1, fun h => hy (by linear_combination h),
        pair_eq hx (by ring)⟩
    · exact Or.inr (Or.inr (Or.inl hz))
    · exact Or.inr (Or.inr (Or.inr hz))
  · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | rfl | rfl)
    · exact Or.inr (Or.inl ⟨rfl,
        show r - 1 ≠ (2 : ZMod m) from fun h => hr (by linear_combination h)⟩)
    · exact Or.inl ⟨rfl,
        show r - 2 ≠ (1 : ZMod m) from fun h => hr (by linear_combination h)⟩
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

/-- The active set is exactly the closed-form endpoint family: the
`A_c(r)` and `B_c(r)` strings away from the collision index, together
with the two puncture endpoints `E⁺_c` and `E⁻_c`. -/
theorem activePred_iff_endpoint {m : Nat} [NeZero m] (_hm : 6 ≤ m)
    (c : TorusColor 3) (z : TerminalQ m) :
    activePred c z ↔
      (∃ r, r ≠ TerminalA2EndpointRank.endpointCollisionIndex (m := m) c ∧
        z = D3TerminalA2Parametric.terminalEndpointA (m := m) c r) ∨
      (∃ r, r ≠ TerminalA2EndpointRank.endpointCollisionIndex (m := m) c ∧
        z = D3TerminalA2Parametric.terminalEndpointB (m := m) c r) ∨
      z = D3TerminalA2Parametric.terminalEndpointEplus (m := m) c ∨
      z = D3TerminalA2Parametric.terminalEndpointEminus (m := m) c := by
  fin_cases c
  · exact endpoint_iff0 z
  · exact endpoint_iff1 z
  · exact endpoint_iff2 z

/-! ## Endpoints sit on the expected fibers -/

/-- `A_c(r)` lies on the fiber labelled `r`. -/
theorem terminalFiberLabel_endpointA {m : Nat} (c : TorusColor 3)
    (r : ZMod m) :
    D3TerminalA2Parametric.terminalFiberLabel c
      (D3TerminalA2Parametric.terminalEndpointA (m := m) c r) = r := by
  fin_cases c
  · rfl
  · rfl
  · change (1 : ZMod m) + (r - 1) = r
    ring

/-- `B_c(r)` lies on the fiber labelled `r`. -/
theorem terminalFiberLabel_endpointB {m : Nat} (c : TorusColor 3)
    (r : ZMod m) :
    D3TerminalA2Parametric.terminalFiberLabel c
      (D3TerminalA2Parametric.terminalEndpointB (m := m) c r) = r := by
  fin_cases c
  · rfl
  · rfl
  · change (r - 2) + (2 : ZMod m) = r
    ring

/-- `E⁺_c` lies on the collision fiber. -/
theorem terminalFiberLabel_endpointEplus {m : Nat} (c : TorusColor 3) :
    D3TerminalA2Parametric.terminalFiberLabel c
        (D3TerminalA2Parametric.terminalEndpointEplus (m := m) c) =
      TerminalA2EndpointRank.endpointCollisionIndex (m := m) c := by
  fin_cases c
  · rfl
  · rfl
  · change (2 : ZMod m) + 1 = (3 : ZMod m)
    ring

/-- `E⁻_c` lies on the collision fiber. -/
theorem terminalFiberLabel_endpointEminus {m : Nat} (c : TorusColor 3) :
    D3TerminalA2Parametric.terminalFiberLabel c
        (D3TerminalA2Parametric.terminalEndpointEminus (m := m) c) =
      TerminalA2EndpointRank.endpointCollisionIndex (m := m) c := by
  fin_cases c
  · rfl
  · rfl
  · change (0 : ZMod m) + 3 = (3 : ZMod m)
    ring

/-! ## Per-fiber pairing -/

private theorem genericFiber0 {m : Nat} [NeZero m] {g : ZMod m}
    (hg : g ≠ (2 : ZMod m)) (z : TerminalQ m) :
    ((z.2 = 2 ∧ z.1 ≠ 2) ∨ (z.1 + z.2 = 4 ∧ z.1 ≠ 2) ∨
        z = ((2 : ZMod m), (1 : ZMod m)) ∨
        z = ((2 : ZMod m), (3 : ZMod m))) ∧ z.1 = g ↔
      z = ((g, 2) : TerminalQ m) ∨ z = ((g, 4 - g) : TerminalQ m) := by
  constructor
  · rintro ⟨⟨hy, hx⟩ | ⟨hs, hx⟩ | hz | hz, hfib⟩
    · exact Or.inl (pair_eq hfib hy)
    · exact Or.inr (pair_eq hfib (by linear_combination hs - hfib))
    · exact absurd (hfib.symm.trans (by rw [hz])) hg
    · exact absurd (hfib.symm.trans (by rw [hz])) hg
  · rintro (rfl | rfl)
    · exact ⟨Or.inl ⟨rfl, hg⟩, rfl⟩
    · exact ⟨Or.inr (Or.inl ⟨show g + (4 - g) = (4 : ZMod m) by ring, hg⟩),
        rfl⟩

private theorem genericFiber1 {m : Nat} [NeZero m] {g : ZMod m}
    (hg : g ≠ (3 : ZMod m)) (z : TerminalQ m) :
    ((z.1 = 1 ∧ z.2 ≠ 3) ∨ (z.1 + z.2 = 4 ∧ z.2 ≠ 3) ∨
        z = ((0 : ZMod m), (3 : ZMod m)) ∨
        z = ((2 : ZMod m), (3 : ZMod m))) ∧ z.2 = g ↔
      z = ((1, g) : TerminalQ m) ∨ z = ((4 - g, g) : TerminalQ m) := by
  constructor
  · rintro ⟨⟨hx, hy⟩ | ⟨hs, hy⟩ | hz | hz, hfib⟩
    · exact Or.inl (pair_eq hx hfib)
    · exact Or.inr (pair_eq (by linear_combination hs - hfib) hfib)
    · exact absurd (hfib.symm.trans (by rw [hz])) hg
    · exact absurd (hfib.symm.trans (by rw [hz])) hg
  · rintro (rfl | rfl)
    · exact ⟨Or.inl ⟨rfl, hg⟩, rfl⟩
    · exact ⟨Or.inr (Or.inl ⟨show (4 : ZMod m) - g + g = 4 by ring, hg⟩),
        rfl⟩

private theorem genericFiber2 {m : Nat} [NeZero m] {g : ZMod m}
    (hg : g ≠ (3 : ZMod m)) (z : TerminalQ m) :
    ((z.2 = 2 ∧ z.1 ≠ 1) ∨ (z.1 = 1 ∧ z.2 ≠ 2) ∨
        z = ((2 : ZMod m), (1 : ZMod m)) ∨
        z = ((0 : ZMod m), (3 : ZMod m))) ∧ z.1 + z.2 = g ↔
      z = ((1, g - 1) : TerminalQ m) ∨ z = ((g - 2, 2) : TerminalQ m) := by
  constructor
  · rintro ⟨⟨hy, hx⟩ | ⟨hx, hy⟩ | hz | hz, hfib⟩
    · exact Or.inr (pair_eq (by linear_combination hfib - hy) hy)
    · exact Or.inl (pair_eq hx (by linear_combination hfib - hx))
    · exact absurd (show g = (3 : ZMod m) by rw [← hfib, hz]; ring) hg
    · exact absurd (show g = (3 : ZMod m) by rw [← hfib, hz]; ring) hg
  · rintro (rfl | rfl)
    · exact ⟨Or.inr (Or.inl ⟨rfl,
          show g - 1 ≠ (2 : ZMod m) from
            fun h => hg (by linear_combination h)⟩),
        show (1 : ZMod m) + (g - 1) = g by ring⟩
    · exact ⟨Or.inl ⟨rfl,
          show g - 2 ≠ (1 : ZMod m) from
            fun h => hg (by linear_combination h)⟩,
        show g - 2 + (2 : ZMod m) = g by ring⟩

private theorem collisionFiber0 {m : Nat} [NeZero m] (z : TerminalQ m) :
    ((z.2 = 2 ∧ z.1 ≠ 2) ∨ (z.1 + z.2 = 4 ∧ z.1 ≠ 2) ∨
        z = ((2 : ZMod m), (1 : ZMod m)) ∨
        z = ((2 : ZMod m), (3 : ZMod m))) ∧ z.1 = (2 : ZMod m) ↔
      z = ((2 : ZMod m), (3 : ZMod m)) ∨
        z = ((2 : ZMod m), (1 : ZMod m)) := by
  constructor
  · rintro ⟨⟨hy, hx⟩ | ⟨hs, hx⟩ | hz | hz, hfib⟩
    · exact absurd hfib hx
    · exact absurd hfib hx
    · exact Or.inr hz
    · exact Or.inl hz
  · rintro (rfl | rfl)
    · exact ⟨Or.inr (Or.inr (Or.inr rfl)), rfl⟩
    · exact ⟨Or.inr (Or.inr (Or.inl rfl)), rfl⟩

private theorem collisionFiber1 {m : Nat} [NeZero m] (z : TerminalQ m) :
    ((z.1 = 1 ∧ z.2 ≠ 3) ∨ (z.1 + z.2 = 4 ∧ z.2 ≠ 3) ∨
        z = ((0 : ZMod m), (3 : ZMod m)) ∨
        z = ((2 : ZMod m), (3 : ZMod m))) ∧ z.2 = (3 : ZMod m) ↔
      z = ((0 : ZMod m), (3 : ZMod m)) ∨
        z = ((2 : ZMod m), (3 : ZMod m)) := by
  constructor
  · rintro ⟨⟨hx, hy⟩ | ⟨hs, hy⟩ | hz | hz, hfib⟩
    · exact absurd hfib hy
    · exact absurd hfib hy
    · exact Or.inl hz
    · exact Or.inr hz
  · rintro (rfl | rfl)
    · exact ⟨Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨Or.inr (Or.inr (Or.inr rfl)), rfl⟩

private theorem collisionFiber2 {m : Nat} [NeZero m] (z : TerminalQ m) :
    ((z.2 = 2 ∧ z.1 ≠ 1) ∨ (z.1 = 1 ∧ z.2 ≠ 2) ∨
        z = ((2 : ZMod m), (1 : ZMod m)) ∨
        z = ((0 : ZMod m), (3 : ZMod m))) ∧ z.1 + z.2 = (3 : ZMod m) ↔
      z = ((2 : ZMod m), (1 : ZMod m)) ∨
        z = ((0 : ZMod m), (3 : ZMod m)) := by
  constructor
  · rintro ⟨⟨hy, hx⟩ | ⟨hx, hy⟩ | hz | hz, hfib⟩
    · exact absurd (by linear_combination hfib - hy) hx
    · exact absurd (by linear_combination hfib - hx) hy
    · exact Or.inl hz
    · exact Or.inr hz
  · rintro (rfl | rfl)
    · exact ⟨Or.inr (Or.inr (Or.inl rfl)),
        show (2 : ZMod m) + 1 = 3 by ring⟩
    · exact ⟨Or.inr (Or.inr (Or.inr rfl)),
        show (0 : ZMod m) + 3 = 3 by ring⟩

/-- On a generic fiber `g` (away from the collision index) the active
points are exactly the endpoint pair `A_c(g)`, `B_c(g)`. -/
theorem active_iff_pair_on_generic_fiber {m : Nat} [NeZero m]
    (_hm : 6 ≤ m) (c : TorusColor 3) {g : ZMod m}
    (hg : g ≠ TerminalA2EndpointRank.endpointCollisionIndex (m := m) c)
    (z : TerminalQ m) :
    activePred c z ∧ D3TerminalA2Parametric.terminalFiberLabel c z = g ↔
      z = D3TerminalA2Parametric.terminalEndpointA (m := m) c g ∨
        z = D3TerminalA2Parametric.terminalEndpointB (m := m) c g := by
  fin_cases c
  · exact genericFiber0 hg z
  · exact genericFiber1 hg z
  · exact genericFiber2 hg z

/-- On the collision fiber the active points are exactly the puncture
pair `E⁺_c`, `E⁻_c`. -/
theorem active_iff_pair_on_collision_fiber {m : Nat} [NeZero m]
    (_hm : 6 ≤ m) (c : TorusColor 3) (z : TerminalQ m) :
    activePred c z ∧
        D3TerminalA2Parametric.terminalFiberLabel c z =
          TerminalA2EndpointRank.endpointCollisionIndex (m := m) c ↔
      z = D3TerminalA2Parametric.terminalEndpointEplus (m := m) c ∨
        z = D3TerminalA2Parametric.terminalEndpointEminus (m := m) c := by
  fin_cases c
  · exact collisionFiber0 z
  · exact collisionFiber1 z
  · exact collisionFiber2 z

/-- The generic-fiber pair is a genuine pair: `A_c(g) ≠ B_c(g)` away from
the collision index. -/
theorem endpointA_ne_endpointB_of_ne_collision {m : Nat} [NeZero m]
    (c : TorusColor 3) {g : ZMod m}
    (hg : g ≠ TerminalA2EndpointRank.endpointCollisionIndex (m := m) c) :
    D3TerminalA2Parametric.terminalEndpointA (m := m) c g ≠
      D3TerminalA2Parametric.terminalEndpointB (m := m) c g := by
  fin_cases c
  · exact pair_ne_right fun h =>
      (show g ≠ (2 : ZMod m) from hg) (by linear_combination h)
  · exact pair_ne_left fun h =>
      (show g ≠ (3 : ZMod m) from hg) (by linear_combination h)
  · exact pair_ne_left fun h =>
      (show g ≠ (3 : ZMod m) from hg) (by linear_combination -h)

/-- The collision-fiber pair is a genuine pair: `E⁺_c ≠ E⁻_c` for
`m ≥ 6`. -/
theorem endpointEplus_ne_endpointEminus {m : Nat} [NeZero m] (hm : 6 ≤ m)
    (c : TorusColor 3) :
    D3TerminalA2Parametric.terminalEndpointEplus (m := m) c ≠
      D3TerminalA2Parametric.terminalEndpointEminus (m := m) c := by
  fin_cases c
  · exact pair_ne_right ((zNe13 hm).symm)
  · exact pair_ne_left (zNe02 hm)
  · exact pair_ne_left ((zNe02 hm).symm)

end TerminalA2ActiveSet
end V28Hard
end EvenV11
