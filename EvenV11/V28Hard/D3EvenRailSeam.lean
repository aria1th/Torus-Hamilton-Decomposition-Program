import EvenV11.V28Hard.D3TerminalA2Parametric

/-!
# D3-even rail seam: the wild layer's combinatorics (module 1)

This file implements the seam data layer of the rail-seam D3-even schedule
(`docs/WILDE_SEARCH_20260610.md` §3, §4 item 1; numeric ground truth:
`scripts/search_d3_even_dir.py construct`).  Everything is stated in the
manuscript pair coordinates `TerminalQ m = (ZMod m)²`; the standard root
section is reached through `D3TerminalA2Parametric.rootPairEquiv` at the end.

Contents:

* the three rails `P` (01-swap cells), `Q` (02-swap cells), `S` (12-swap
  cells) as decidable predicates `memP/memQ/memS` and Finsets
  `railP/railQ/railS`, with cardinality `m`, pairwise disjointness and the
  classification lemma;
* the wild row `wildRow : (ZMod m)² → Equiv.Perm (Fin 3)` (identity off
  `P ∪ Q ∪ S`, the transpositions `(01)/(02)/(12)` on `P/Q/S`);
* the per-color deviation maps `rho c : w ↦ w + (e_{wildRow w c} − e_c)`
  with `e₀ = (1,0)`, `e₁ = (0,1)`, `e₂ = (0,0)`;
* the closed-form `2m`-zigzag enumerations `seamPoint0/1/2` (rank lists in
  `ρ_c`-orbit order), their injectivity via explicit inverse ranks
  `seamRank0/1/2`, the rank-step lemmas
  `rho c (seamPoint m c n) = seamPoint m c (seamSucc m n)`, and bijectivity
  of each `rho c`;
* the active-set lemma `rho c w ≠ w ↔ activePred c w ↔ w ∈ range seamPoint`.

All parametric statements hold for every `m ≥ 4` (no parity hypothesis is
needed at this combinatorial layer; evenness only enters the sign/return
analysis of later modules).  Decide anchors at `m = 4` and `m = 6` pin the
closed forms against the script's orbits.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace EvenV11
namespace V28Hard
namespace D3EvenRailSeam

open TerminalA2LowMod

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Small `ZMod` value toolkit -/

section Toolkit

variable {m : Nat} [NeZero m]

private theorem val_natCast {k : Nat} (h : k < m) :
    ((k : ZMod m)).val = k :=
  ZMod.val_natCast_of_lt h

private theorem natCast_sub_eq_neg {k : Nat} (h : k ≤ m) :
    ((m - k : Nat) : ZMod m) = -(k : ZMod m) := by
  apply eq_neg_of_add_eq_zero_left
  have hsum : ((m - k) + k : Nat) = m := by omega
  calc ((m - k : Nat) : ZMod m) + (k : ZMod m)
      = (((m - k) + k : Nat) : ZMod m) := by push_cast; ring
    _ = ((m : Nat) : ZMod m) := by rw [hsum]
    _ = 0 := ZMod.natCast_self m

private theorem val_neg_natCast {k : Nat} (h1 : 1 ≤ k) (h2 : k < m) :
    (-(k : ZMod m)).val = m - k := by
  rw [← natCast_sub_eq_neg (le_of_lt h2)]
  exact val_natCast (by omega)

private theorem natCast_reduce {k : Nat} (h : m ≤ k) :
    ((k : Nat) : ZMod m) = ((k - m : Nat) : ZMod m) := by
  calc ((k : Nat) : ZMod m)
      = (((k - m) + m : Nat) : ZMod m) := by rw [Nat.sub_add_cancel h]
    _ = ((k - m : Nat) : ZMod m) + ((m : Nat) : ZMod m) := by
        push_cast; ring
    _ = ((k - m : Nat) : ZMod m) := by rw [ZMod.natCast_self, add_zero]

private theorem val_natCast_reduce {k : Nat} (h1 : m ≤ k) (h2 : k < 2 * m) :
    ((k : Nat) : ZMod m).val = k - m := by
  rw [natCast_reduce h1]
  exact val_natCast (by omega)

private theorem val_neg_natCast_reduce {k : Nat} (h1 : m + 1 ≤ k)
    (h2 : k ≤ 2 * m - 1) :
    (-(k : ZMod m)).val = 2 * m - k := by
  rw [natCast_reduce (by omega)]
  rw [val_neg_natCast (by omega) (by omega)]
  omega

private theorem neg_natCast_self : -((m : Nat) : ZMod m) = 0 := by
  rw [ZMod.natCast_self, neg_zero]

private theorem val_inj {a b : ZMod m} (h : a.val = b.val) : a = b :=
  ZMod.val_injective m h

private theorem ne_of_val_ne {a b : ZMod m} (h : a.val ≠ b.val) : a ≠ b :=
  fun he => h (congrArg ZMod.val he)

private theorem one_eq_natCast : (1 : ZMod m) = ((1 : Nat) : ZMod m) := by
  norm_cast

private theorem two_eq_natCast : (2 : ZMod m) = ((2 : Nat) : ZMod m) := by
  norm_cast

private theorem three_eq_natCast : (3 : ZMod m) = ((3 : Nat) : ZMod m) := by
  norm_cast

private theorem val0 : (0 : ZMod m).val = 0 := ZMod.val_zero

private theorem val1 (hm : 4 ≤ m) : (1 : ZMod m).val = 1 := by
  rw [one_eq_natCast]; exact val_natCast (by omega)

private theorem val2 (hm : 4 ≤ m) : (2 : ZMod m).val = 2 := by
  rw [two_eq_natCast]; exact val_natCast (by omega)

private theorem val3 (hm : 4 ≤ m) : (3 : ZMod m).val = 3 := by
  rw [three_eq_natCast]; exact val_natCast (by omega)

private theorem valn1 (hm : 4 ≤ m) : (-1 : ZMod m).val = m - 1 := by
  rw [one_eq_natCast]; exact val_neg_natCast (by omega) (by omega)

private theorem valn2 (hm : 4 ≤ m) : (-2 : ZMod m).val = m - 2 := by
  rw [two_eq_natCast]; exact val_neg_natCast (by omega) (by omega)

private theorem valn3 (hm : 4 ≤ m) : (-3 : ZMod m).val = m - 3 := by
  rw [three_eq_natCast]; exact val_neg_natCast (by omega) (by omega)

private theorem pair_ne_fst {x y a b : ZMod m} (h : x.val ≠ a.val) :
    ((x, y) : TerminalQ m) ≠ (a, b) :=
  fun he => h (congrArg (fun p : TerminalQ m => p.1.val) he)

private theorem pair_ne_snd {x y a b : ZMod m} (h : y.val ≠ b.val) :
    ((x, y) : TerminalQ m) ≠ (a, b) :=
  fun he => h (congrArg (fun p : TerminalQ m => p.2.val) he)

private theorem val_pair_of_eq {w : TerminalQ m} {a b : ZMod m}
    (h : w = (a, b)) : w.1.val = a.val ∧ w.2.val = b.val := by
  subst h; exact ⟨rfl, rfl⟩

end Toolkit

/-! ## The three rails -/

section RailDefs

variable {m : Nat}

/-- Membership in the `01`-swap rail
`P = {(0,0)} ∪ {(x,−x) : 3 ≤ x ≤ m−1} ∪ {(1, m−2), (2, m−1)}`. -/
def memP (w : TerminalQ m) : Prop :=
  w = (0, 0) ∨ (w.1 + w.2 = 0 ∧ 3 ≤ w.1.val) ∨ w = (1, -2) ∨ w = (2, -1)

/-- Membership in the `02`-swap rail
`Q = {(x, m−1) : x = 0 ∨ 3 ≤ x ≤ m−1} ∪ {(1, 0), (2, m−2)}`. -/
def memQ (w : TerminalQ m) : Prop :=
  (w.2 = -1 ∧ (w.1 = 0 ∨ 3 ≤ w.1.val)) ∨ w = (1, 0) ∨ w = (2, -2)

/-- Membership in the `12`-swap rail
`S = {(2, y) : 0 ≤ y ≤ m−3} ∪ {(1, m−1), (3, m−2)}`. -/
def memS (w : TerminalQ m) : Prop :=
  (w.1 = 2 ∧ w.2.val ≤ m - 3) ∨ w = (1, -1) ∨ w = (3, -2)

instance : DecidablePred (memP (m := m)) := fun w =>
  inferInstanceAs (Decidable
    (w = (0, 0) ∨ (w.1 + w.2 = 0 ∧ 3 ≤ w.1.val) ∨ w = (1, -2) ∨
      w = (2, -1)))

instance : DecidablePred (memQ (m := m)) := fun w =>
  inferInstanceAs (Decidable
    ((w.2 = -1 ∧ (w.1 = 0 ∨ 3 ≤ w.1.val)) ∨ w = (1, 0) ∨ w = (2, -2)))

instance : DecidablePred (memS (m := m)) := fun w =>
  inferInstanceAs (Decidable
    ((w.1 = 2 ∧ w.2.val ≤ m - 3) ∨ w = (1, -1) ∨ w = (3, -2)))

end RailDefs

section RailMembers

variable {m : Nat} [NeZero m]

private theorem memP_zero : memP ((0, 0) : TerminalQ m) := Or.inl rfl

private theorem memP_one : memP ((1, -2) : TerminalQ m) :=
  Or.inr (Or.inr (Or.inl rfl))

private theorem memP_two : memP ((2, -1) : TerminalQ m) :=
  Or.inr (Or.inr (Or.inr rfl))

private theorem memP_anti {x y : ZMod m} (hsum : x + y = 0)
    (hx : 3 ≤ x.val) : memP (x, y) :=
  Or.inr (Or.inl ⟨hsum, hx⟩)

private theorem memQ_row {x : ZMod m} (hx : x = 0 ∨ 3 ≤ x.val) :
    memQ ((x, -1) : TerminalQ m) := Or.inl ⟨rfl, hx⟩

private theorem memQ_one : memQ ((1, 0) : TerminalQ m) := Or.inr (Or.inl rfl)

private theorem memQ_two : memQ ((2, -2) : TerminalQ m) :=
  Or.inr (Or.inr rfl)

private theorem memS_col {y : ZMod m} (hy : y.val ≤ m - 3) :
    memS ((2, y) : TerminalQ m) := Or.inl ⟨rfl, hy⟩

private theorem memS_one : memS ((1, -1) : TerminalQ m) := Or.inr (Or.inl rfl)

private theorem memS_three : memS ((3, -2) : TerminalQ m) :=
  Or.inr (Or.inr rfl)

/-- `P`-membership in coordinate-value form. -/
private theorem memP_val (hm : 4 ≤ m) {w : TerminalQ m} (h : memP w) :
    (w.1.val = 0 ∧ w.2.val = 0) ∨
      (3 ≤ w.1.val ∧ w.1.val < m ∧ w.2.val = m - w.1.val) ∨
      (w.1.val = 1 ∧ w.2.val = m - 2) ∨
      (w.1.val = 2 ∧ w.2.val = m - 1) := by
  rcases h with h | ⟨hsum, hx⟩ | h | h
  · obtain ⟨h1, h2⟩ := val_pair_of_eq h
    rw [val0] at h1 h2
    exact Or.inl ⟨h1, h2⟩
  · have hlt := ZMod.val_lt w.1
    have hw2 : w.2 = -w.1 := by linear_combination hsum
    have hval : w.2.val = m - w.1.val := by
      calc w.2.val = (-w.1).val := by rw [hw2]
        _ = (-((w.1.val : Nat) : ZMod m)).val := by
            rw [ZMod.natCast_zmod_val]
        _ = m - w.1.val := val_neg_natCast (by omega) hlt
    exact Or.inr (Or.inl ⟨hx, hlt, hval⟩)
  · obtain ⟨h1, h2⟩ := val_pair_of_eq h
    rw [val1 hm] at h1; rw [valn2 hm] at h2
    exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
  · obtain ⟨h1, h2⟩ := val_pair_of_eq h
    rw [val2 hm] at h1; rw [valn1 hm] at h2
    exact Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))

/-- `Q`-membership in coordinate-value form. -/
private theorem memQ_val (hm : 4 ≤ m) {w : TerminalQ m} (h : memQ w) :
    (w.2.val = m - 1 ∧ (w.1.val = 0 ∨ (3 ≤ w.1.val ∧ w.1.val < m))) ∨
      (w.1.val = 1 ∧ w.2.val = 0) ∨
      (w.1.val = 2 ∧ w.2.val = m - 2) := by
  rcases h with ⟨h1, h2⟩ | h | h
  · have hv2 : w.2.val = m - 1 := by
      have := congrArg ZMod.val h1
      rwa [valn1 hm] at this
    rcases h2 with h2 | h2
    · have hv1 : w.1.val = 0 := by
        have := congrArg ZMod.val h2
        rwa [val0] at this
      exact Or.inl ⟨hv2, Or.inl hv1⟩
    · exact Or.inl ⟨hv2, Or.inr ⟨h2, ZMod.val_lt w.1⟩⟩
  · obtain ⟨h1, h2⟩ := val_pair_of_eq h
    rw [val1 hm] at h1; rw [val0] at h2
    exact Or.inr (Or.inl ⟨h1, h2⟩)
  · obtain ⟨h1, h2⟩ := val_pair_of_eq h
    rw [val2 hm] at h1; rw [valn2 hm] at h2
    exact Or.inr (Or.inr ⟨h1, h2⟩)

/-- `S`-membership in coordinate-value form. -/
private theorem memS_val (hm : 4 ≤ m) {w : TerminalQ m} (h : memS w) :
    (w.1.val = 2 ∧ w.2.val ≤ m - 3) ∨
      (w.1.val = 1 ∧ w.2.val = m - 1) ∨
      (w.1.val = 3 ∧ w.2.val = m - 2) := by
  rcases h with ⟨h1, h2⟩ | h | h
  · have hv1 : w.1.val = 2 := by
      have := congrArg ZMod.val h1
      rwa [val2 hm] at this
    exact Or.inl ⟨hv1, h2⟩
  · obtain ⟨h1, h2⟩ := val_pair_of_eq h
    rw [val1 hm] at h1; rw [valn1 hm] at h2
    exact Or.inr (Or.inl ⟨h1, h2⟩)
  · obtain ⟨h1, h2⟩ := val_pair_of_eq h
    rw [val3 hm] at h1; rw [valn2 hm] at h2
    exact Or.inr (Or.inr ⟨h1, h2⟩)

/-- The rails `P` and `Q` are disjoint. -/
theorem memP_memQ_false {m : Nat} [NeZero m] (hm : 4 ≤ m)
    {w : TerminalQ m} (hp : memP w) (hq : memQ w) : False := by
  rcases memP_val hm hp with ⟨h1, h2⟩ | ⟨h1, h1', h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ <;>
    rcases memQ_val hm hq with ⟨h3, h4 | ⟨h4, h4'⟩⟩ | ⟨h3, h4⟩ |
      ⟨h3, h4⟩ <;> omega

/-- The rails `P` and `S` are disjoint. -/
theorem memP_memS_false {m : Nat} [NeZero m] (hm : 4 ≤ m)
    {w : TerminalQ m} (hp : memP w) (hs : memS w) : False := by
  rcases memP_val hm hp with ⟨h1, h2⟩ | ⟨h1, h1', h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ <;>
    rcases memS_val hm hs with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega

/-- The rails `Q` and `S` are disjoint. -/
theorem memQ_memS_false {m : Nat} [NeZero m] (hm : 4 ≤ m)
    {w : TerminalQ m} (hq : memQ w) (hs : memS w) : False := by
  rcases memQ_val hm hq with ⟨h1, h2 | ⟨h2, h2'⟩⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ <;>
    rcases memS_val hm hs with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega

/-- Classification: every cell lies in exactly one rail or in none. -/
theorem rail_classification {m : Nat} [NeZero m] (hm : 4 ≤ m)
    (w : TerminalQ m) :
    (memP w ∧ ¬memQ w ∧ ¬memS w) ∨ (¬memP w ∧ memQ w ∧ ¬memS w) ∨
      (¬memP w ∧ ¬memQ w ∧ memS w) ∨ (¬memP w ∧ ¬memQ w ∧ ¬memS w) := by
  by_cases hp : memP w
  · exact Or.inl ⟨hp, fun hq => memP_memQ_false hm hp hq,
      fun hs => memP_memS_false hm hp hs⟩
  by_cases hq : memQ w
  · exact Or.inr (Or.inl ⟨hp, hq, fun hs => memQ_memS_false hm hq hs⟩)
  by_cases hs : memS w
  · exact Or.inr (Or.inr (Or.inl ⟨hp, hq, hs⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hp, hq, hs⟩))

end RailMembers

/-! ## The wild row and the deviation maps -/

section WildRow

variable {m : Nat}

/-- Direction vectors `e₀ = (1,0)`, `e₁ = (0,1)`, `e₂ = (0,0)`. -/
def eVec : Fin 3 → TerminalQ m
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (0, 0)

/-- The wild row: the transposition `(01)` on `P`, `(02)` on `Q`, `(12)` on
`S`, and the identity off `P ∪ Q ∪ S`.  Values are permutations, so the
Latin property of the wild layer is immediate. -/
def wildRow (w : TerminalQ m) : Equiv.Perm (Fin 3) :=
  if memP w then Equiv.swap 0 1
  else if memQ w then Equiv.swap 0 2
  else if memS w then Equiv.swap 1 2
  else 1

/-- RF1 for the wild row, for free: each cell's color table is a bijection. -/
theorem wildRow_latin (w : TerminalQ m) :
    Function.Bijective (wildRow w) :=
  (wildRow w).bijective

/-- The color-`c` deviation of the wild layer relative to the identity
base: `w ↦ w + (e_{wildRow w c} − e_c)`. -/
def rho (c : Fin 3) (w : TerminalQ m) : TerminalQ m :=
  w + (eVec (wildRow w c) - eVec c)

theorem wildRow_of_memP {w : TerminalQ m} (hp : memP w) :
    wildRow w = Equiv.swap 0 1 := by
  unfold wildRow
  rw [if_pos hp]

theorem wildRow_of_memQ {m : Nat} [NeZero m] (hm : 4 ≤ m)
    {w : TerminalQ m} (hq : memQ w) : wildRow w = Equiv.swap 0 2 := by
  unfold wildRow
  rw [if_neg (fun hp => memP_memQ_false hm hp hq), if_pos hq]

theorem wildRow_of_memS {m : Nat} [NeZero m] (hm : 4 ≤ m)
    {w : TerminalQ m} (hs : memS w) : wildRow w = Equiv.swap 1 2 := by
  unfold wildRow
  rw [if_neg (fun hp => memP_memS_false hm hp hs),
    if_neg (fun hq => memQ_memS_false hm hq hs), if_pos hs]

theorem wildRow_of_off {w : TerminalQ m} (h1 : ¬memP w) (h2 : ¬memQ w)
    (h3 : ¬memS w) : wildRow w = 1 := by
  unfold wildRow
  rw [if_neg h1, if_neg h2, if_neg h3]

/-- Off all three rails every deviation fixes the cell. -/
theorem rho_of_off {w : TerminalQ m} (h1 : ¬memP w) (h2 : ¬memQ w)
    (h3 : ¬memS w) (c : Fin 3) : rho c w = w := by
  unfold rho
  rw [wildRow_of_off h1 h2 h3, Equiv.Perm.one_apply, sub_self, add_zero]

end WildRow

section KickLemmas

variable {m : Nat} [NeZero m]

/-- `ρ₀` kicks `P`-cells by `e₁ − e₀ = (−1, 1)`. -/
theorem rho_zero_of_memP {a b : ZMod m} (hp : memP (a, b)) :
    rho 0 (a, b) = (a - 1, b + 1) := by
  unfold rho
  rw [wildRow_of_memP hp,
    show (Equiv.swap (0 : Fin 3) 1) 0 = 1 from by decide,
    show (eVec 1 : TerminalQ m) = (0, 1) from rfl,
    show (eVec 0 : TerminalQ m) = (1, 0) from rfl,
    Prod.mk_sub_mk, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> ring

/-- `ρ₀` kicks `Q`-cells by `e₂ − e₀ = (−1, 0)`. -/
theorem rho_zero_of_memQ (hm : 4 ≤ m) {a b : ZMod m}
    (hq : memQ (a, b)) : rho 0 (a, b) = (a - 1, b) := by
  unfold rho
  rw [wildRow_of_memQ hm hq,
    show (Equiv.swap (0 : Fin 3) 2) 0 = 2 from by decide,
    show (eVec 2 : TerminalQ m) = (0, 0) from rfl,
    show (eVec 0 : TerminalQ m) = (1, 0) from rfl,
    Prod.mk_sub_mk, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> ring

/-- `ρ₀` fixes `S`-cells. -/
theorem rho_zero_of_memS (hm : 4 ≤ m) {w : TerminalQ m}
    (hs : memS w) : rho 0 w = w := by
  unfold rho
  rw [wildRow_of_memS hm hs,
    show (Equiv.swap (1 : Fin 3) 2) 0 = 0 from by decide,
    sub_self, add_zero]

/-- `ρ₁` kicks `P`-cells by `e₀ − e₁ = (1, −1)`. -/
theorem rho_one_of_memP {a b : ZMod m} (hp : memP (a, b)) :
    rho 1 (a, b) = (a + 1, b - 1) := by
  unfold rho
  rw [wildRow_of_memP hp,
    show (Equiv.swap (0 : Fin 3) 1) 1 = 0 from by decide,
    show (eVec 0 : TerminalQ m) = (1, 0) from rfl,
    show (eVec 1 : TerminalQ m) = (0, 1) from rfl,
    Prod.mk_sub_mk, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> ring

/-- `ρ₁` kicks `S`-cells by `e₂ − e₁ = (0, −1)`. -/
theorem rho_one_of_memS (hm : 4 ≤ m) {a b : ZMod m}
    (hs : memS (a, b)) : rho 1 (a, b) = (a, b - 1) := by
  unfold rho
  rw [wildRow_of_memS hm hs,
    show (Equiv.swap (1 : Fin 3) 2) 1 = 2 from by decide,
    show (eVec 2 : TerminalQ m) = (0, 0) from rfl,
    show (eVec 1 : TerminalQ m) = (0, 1) from rfl,
    Prod.mk_sub_mk, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> ring

/-- `ρ₁` fixes `Q`-cells. -/
theorem rho_one_of_memQ (hm : 4 ≤ m) {w : TerminalQ m}
    (hq : memQ w) : rho 1 w = w := by
  unfold rho
  rw [wildRow_of_memQ hm hq,
    show (Equiv.swap (0 : Fin 3) 2) 1 = 1 from by decide,
    sub_self, add_zero]

/-- `ρ₂` kicks `Q`-cells by `e₀ − e₂ = (1, 0)`. -/
theorem rho_two_of_memQ (hm : 4 ≤ m) {a b : ZMod m}
    (hq : memQ (a, b)) : rho 2 (a, b) = (a + 1, b) := by
  unfold rho
  rw [wildRow_of_memQ hm hq,
    show (Equiv.swap (0 : Fin 3) 2) 2 = 0 from by decide,
    show (eVec 0 : TerminalQ m) = (1, 0) from rfl,
    show (eVec 2 : TerminalQ m) = (0, 0) from rfl,
    Prod.mk_sub_mk, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> ring

/-- `ρ₂` kicks `S`-cells by `e₁ − e₂ = (0, 1)`. -/
theorem rho_two_of_memS (hm : 4 ≤ m) {a b : ZMod m}
    (hs : memS (a, b)) : rho 2 (a, b) = (a, b + 1) := by
  unfold rho
  rw [wildRow_of_memS hm hs,
    show (Equiv.swap (1 : Fin 3) 2) 2 = 1 from by decide,
    show (eVec 1 : TerminalQ m) = (0, 1) from rfl,
    show (eVec 2 : TerminalQ m) = (0, 0) from rfl,
    Prod.mk_sub_mk, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> ring

/-- `ρ₂` fixes `P`-cells. -/
theorem rho_two_of_memP {w : TerminalQ m} (hp : memP w) :
    rho 2 w = w := by
  unfold rho
  rw [wildRow_of_memP hp,
    show (Equiv.swap (0 : Fin 3) 1) 2 = 2 from by decide,
    sub_self, add_zero]

end KickLemmas

/-! ## Seam labels and the closed-form zigzag enumerations

Each `ρ_c` has a unique nontrivial cycle, of length `2m`.  The closed forms
below list it in orbit order; they are transcriptions of the orbits printed
by `scripts/search_d3_even_dir.py` (verified there for `m ∈ [4, 60]`).  The
`Nat`-indexed cores keep all case analysis at the `Nat` level. -/

/-- Rank labels for a `2m`-zigzag. -/
abbrev SeamLabel (m : Nat) := Fin (2 * m)

/-- Cyclic successor on seam labels. -/
def seamSucc (m : Nat) (n : SeamLabel m) : SeamLabel m :=
  ⟨(n.val + 1) % (2 * m), Nat.mod_lt _ (by have := n.isLt; omega)⟩

theorem seamSucc_val_of_lt {m : Nat} {n : SeamLabel m}
    (h : n.val + 1 < 2 * m) : (seamSucc m n).val = n.val + 1 :=
  Nat.mod_eq_of_lt h

theorem seamSucc_val_last {m : Nat} {n : SeamLabel m}
    (h : n.val = 2 * m - 1) : (seamSucc m n).val = 0 := by
  have hlt := n.isLt
  change (n.val + 1) % (2 * m) = 0
  rw [h, show 2 * m - 1 + 1 = 2 * m from by omega, Nat.mod_self]

theorem seamSucc_injective (m : Nat) : Function.Injective (seamSucc m) := by
  intro a b h
  have ha := a.isLt
  have hb := b.isLt
  have hv := congrArg Fin.val h
  apply Fin.ext
  by_cases h1 : a.val + 1 < 2 * m <;> by_cases h2 : b.val + 1 < 2 * m
  · rw [seamSucc_val_of_lt h1, seamSucc_val_of_lt h2] at hv; omega
  · rw [seamSucc_val_of_lt h1, seamSucc_val_last (by omega)] at hv; omega
  · rw [seamSucc_val_last (by omega), seamSucc_val_of_lt h2] at hv; omega
  · omega

theorem seamSucc_ne {m : Nat} (n : SeamLabel m) : seamSucc m n ≠ n := by
  intro h
  have hlt := n.isLt
  have hv := congrArg Fin.val h
  by_cases h1 : n.val + 1 < 2 * m
  · rw [seamSucc_val_of_lt h1] at hv; omega
  · rw [seamSucc_val_last (by omega)] at hv; omega

/-- `Nat`-indexed core of the `ρ₀` zigzag (through `P ∪ Q`):
ranks `[0, m−2]` walk the `P` anti-diagonal from `(0,0)` to `(2, −2)` (the
last point being the `Q` pivot), `m−1 ↦ (1, −2)`, ranks `[m, 2m−2]` walk
the `Q` row `y = −1` from `(0, −1)` to `(2, −1)` (the last point being the
`P` pivot), and `2m−1 ↦ (1, 0)`. -/
def seamPoint0Nat (m k : Nat) : TerminalQ m :=
  if k = m - 1 then (1, -2)
  else if k = 2 * m - 2 then (2, -1)
  else if k = 2 * m - 1 then (1, 0)
  else if k < m - 1 then (-(k : ZMod m), (k : ZMod m))
  else (-(k : ZMod m), -1)

/-- The `ρ₀` zigzag through `P ∪ Q`, in orbit order. -/
def seamPoint0 (m : Nat) (n : SeamLabel m) : TerminalQ m :=
  seamPoint0Nat m n.val

/-- `Nat`-indexed core of the `ρ₁` zigzag (through `P ∪ S`):
`0 ↦ (0,0)`, `1 ↦ (1, −1)`, `2 ↦ (1, −2)`, ranks `[3, m]` walk the `S`
column `x = 2` downward from `(2, −3)` to `(2, 0)`, `m+1 ↦ (2, −1)`,
`m+2 ↦ (3, −2)`, and ranks `[m+3, 2m−1]` walk the `P` anti-diagonal from
`(3, −3)` up to `(−1, 1)`. -/
def seamPoint1Nat (m k : Nat) : TerminalQ m :=
  if k = 0 then (0, 0)
  else if k = 1 then (1, -1)
  else if k = 2 then (1, -2)
  else if k = m + 1 then (2, -1)
  else if k = m + 2 then (3, -2)
  else if k ≤ m then (2, -(k : ZMod m))
  else ((k : ZMod m), -(k : ZMod m))

/-- The `ρ₁` zigzag through `P ∪ S`, in orbit order. -/
def seamPoint1 (m : Nat) (n : SeamLabel m) : TerminalQ m :=
  seamPoint1Nat m n.val

/-- `Nat`-indexed core of the `ρ₂` zigzag (through `Q ∪ S`):
ranks `[0, m−2]` walk the `S` column `x = 2` upward from `(2, 0)` to
`(2, −2)` (the last point being the `Q` pivot), `m−1 ↦ (3, −2)`, ranks
`[m, 2m−3]` walk the `Q` row `y = −1` from `(3, −1)` around to `(0, −1)`,
`2m−2 ↦ (1, −1)`, and `2m−1 ↦ (1, 0)`. -/
def seamPoint2Nat (m k : Nat) : TerminalQ m :=
  if k = m - 1 then (3, -2)
  else if k = 2 * m - 3 then (0, -1)
  else if k = 2 * m - 2 then (1, -1)
  else if k = 2 * m - 1 then (1, 0)
  else if k ≤ m - 2 then (2, (k : ZMod m))
  else ((k : ZMod m) + 3, -1)

/-- The `ρ₂` zigzag through `Q ∪ S`, in orbit order. -/
def seamPoint2 (m : Nat) (n : SeamLabel m) : TerminalQ m :=
  seamPoint2Nat m n.val

/-! ## Branch evaluation lemmas for the closed forms -/

section EvalLemmas

variable {m : Nat} [NeZero m]

private theorem seamPoint0Nat_anti (hm : 4 ≤ m) {k : Nat}
    (hk : k ≤ m - 2) :
    seamPoint0Nat m k = (-(k : ZMod m), (k : ZMod m)) := by
  unfold seamPoint0Nat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]

private theorem seamPoint0Nat_mid (hm : 4 ≤ m) {k : Nat}
    (hk : k = m - 1) : seamPoint0Nat m k = (1, -2) := by
  unfold seamPoint0Nat
  rw [if_pos hk]

private theorem seamPoint0Nat_row (hm : 4 ≤ m) {k : Nat} (h1 : m ≤ k)
    (h2 : k ≤ 2 * m - 2) :
    seamPoint0Nat m k = (-(k : ZMod m), -1) := by
  by_cases hk : k = 2 * m - 2
  · unfold seamPoint0Nat
    rw [if_neg (by omega), if_pos hk]
    have hfst : -((k : Nat) : ZMod m) = 2 := by
      rw [hk, natCast_reduce (by omega),
        show 2 * m - 2 - m = m - 2 from by omega,
        natCast_sub_eq_neg (show 2 ≤ m by omega), neg_neg,
        ← two_eq_natCast]
    rw [Prod.mk.injEq]
    exact ⟨hfst.symm, rfl⟩
  · unfold seamPoint0Nat
    rw [if_neg (by omega), if_neg hk, if_neg (by omega),
      if_neg (by omega)]

private theorem seamPoint0Nat_rowEnd (hm : 4 ≤ m) {k : Nat}
    (hk : k = 2 * m - 2) : seamPoint0Nat m k = (2, -1) := by
  unfold seamPoint0Nat
  rw [if_neg (by omega), if_pos hk]

private theorem seamPoint0Nat_last (hm : 4 ≤ m) {k : Nat}
    (hk : k = 2 * m - 1) : seamPoint0Nat m k = (1, 0) := by
  unfold seamPoint0Nat
  rw [if_neg (by omega), if_neg (by omega), if_pos hk]

private theorem seamPoint1Nat_zero (hm : 4 ≤ m) {k : Nat} (hk : k = 0) :
    seamPoint1Nat m k = (0, 0) := by
  unfold seamPoint1Nat
  rw [if_pos hk]

private theorem seamPoint1Nat_one (hm : 4 ≤ m) {k : Nat} (hk : k = 1) :
    seamPoint1Nat m k = (1, -1) := by
  unfold seamPoint1Nat
  rw [if_neg (by omega), if_pos hk]

private theorem seamPoint1Nat_two (hm : 4 ≤ m) {k : Nat} (hk : k = 2) :
    seamPoint1Nat m k = (1, -2) := by
  unfold seamPoint1Nat
  rw [if_neg (by omega), if_neg (by omega), if_pos hk]

private theorem seamPoint1Nat_col (hm : 4 ≤ m) {k : Nat} (h1 : 3 ≤ k)
    (h2 : k ≤ m) : seamPoint1Nat m k = (2, -(k : ZMod m)) := by
  unfold seamPoint1Nat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos h2]

private theorem seamPoint1Nat_colEnd (hm : 4 ≤ m) {k : Nat}
    (hk : k = m + 1) : seamPoint1Nat m k = (2, -1) := by
  unfold seamPoint1Nat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos hk]

private theorem seamPoint1Nat_hop (hm : 4 ≤ m) {k : Nat}
    (hk : k = m + 2) : seamPoint1Nat m k = (3, -2) := by
  unfold seamPoint1Nat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos hk]

private theorem seamPoint1Nat_anti (hm : 4 ≤ m) {k : Nat}
    (h1 : m + 3 ≤ k) (h2 : k ≤ 2 * m - 1) :
    seamPoint1Nat m k = ((k : ZMod m), -(k : ZMod m)) := by
  unfold seamPoint1Nat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private theorem seamPoint2Nat_col (hm : 4 ≤ m) {k : Nat}
    (hk : k ≤ m - 2) : seamPoint2Nat m k = (2, (k : ZMod m)) := by
  unfold seamPoint2Nat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos hk]

private theorem seamPoint2Nat_hop (hm : 4 ≤ m) {k : Nat}
    (hk : k = m - 1) : seamPoint2Nat m k = (3, -2) := by
  unfold seamPoint2Nat
  rw [if_pos hk]

private theorem seamPoint2Nat_row (hm : 4 ≤ m) {k : Nat} (h1 : m ≤ k)
    (h2 : k ≤ 2 * m - 3) :
    seamPoint2Nat m k = ((k : ZMod m) + 3, -1) := by
  by_cases hk : k = 2 * m - 3
  · unfold seamPoint2Nat
    rw [if_neg (by omega), if_pos hk]
    have hfst : ((k : Nat) : ZMod m) + 3 = 0 := by
      rw [hk, natCast_reduce (by omega),
        show 2 * m - 3 - m = m - 3 from by omega, three_eq_natCast]
      calc ((m - 3 : Nat) : ZMod m) + ((3 : Nat) : ZMod m)
          = (((m - 3) + 3 : Nat) : ZMod m) := by push_cast; ring
        _ = ((m : Nat) : ZMod m) := by
            rw [show (m - 3) + 3 = m from by omega]
        _ = 0 := ZMod.natCast_self m
    rw [Prod.mk.injEq]
    exact ⟨hfst.symm, rfl⟩
  · unfold seamPoint2Nat
    rw [if_neg (by omega), if_neg hk, if_neg (by omega),
      if_neg (by omega), if_neg (by omega)]

private theorem seamPoint2Nat_rowZero (hm : 4 ≤ m) {k : Nat}
    (hk : k = 2 * m - 3) : seamPoint2Nat m k = (0, -1) := by
  unfold seamPoint2Nat
  rw [if_neg (by omega), if_pos hk]

private theorem seamPoint2Nat_preLast (hm : 4 ≤ m) {k : Nat}
    (hk : k = 2 * m - 2) : seamPoint2Nat m k = (1, -1) := by
  unfold seamPoint2Nat
  rw [if_neg (by omega), if_neg (by omega), if_pos hk]

private theorem seamPoint2Nat_last (hm : 4 ≤ m) {k : Nat}
    (hk : k = 2 * m - 1) : seamPoint2Nat m k = (1, 0) := by
  unfold seamPoint2Nat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos hk]

end EvalLemmas

/-! ## Run membership lemmas -/

section RunMembers

variable {m : Nat} [NeZero m]

private theorem natCast_m_sub_one (hm : 4 ≤ m) :
    ((m - 1 : Nat) : ZMod m) = -1 := by
  rw [natCast_sub_eq_neg (by omega), ← one_eq_natCast]

private theorem natCast_m_sub_two (hm : 4 ≤ m) :
    ((m - 2 : Nat) : ZMod m) = -2 := by
  rw [natCast_sub_eq_neg (by omega), ← two_eq_natCast]

/-- The end of the `P` anti-diagonal run is the `Q` pivot `(2, −2)`. -/
private theorem pt_anti_end (hm : 4 ≤ m) :
    ((-(((m - 2 : Nat) : ZMod m)), ((m - 2 : Nat) : ZMod m)) :
      TerminalQ m) = (2, -2) := by
  rw [natCast_m_sub_two hm, neg_neg]

private theorem memP_run0 (hm : 4 ≤ m) {k : Nat} (hk : k ≤ m - 3) :
    memP ((-(k : ZMod m), (k : ZMod m)) : TerminalQ m) := by
  rcases Nat.eq_zero_or_pos k with h0 | h1
  · subst h0
    simp only [Nat.cast_zero, neg_zero]
    exact memP_zero
  · exact memP_anti (by ring)
      (by rw [val_neg_natCast h1 (by omega)]; omega)

private theorem memP_runAnti (hm : 4 ≤ m) {k : Nat} (h1 : m + 3 ≤ k)
    (h2 : k ≤ 2 * m - 1) :
    memP (((k : ZMod m), -(k : ZMod m)) : TerminalQ m) :=
  memP_anti (by ring)
    (by rw [val_natCast_reduce (by omega) (by omega)]; omega)

private theorem memQ_rowRun (hm : 4 ≤ m) {k : Nat} (h1 : m ≤ k)
    (h2 : k ≤ 2 * m - 3) :
    memQ ((-(k : ZMod m), -1) : TerminalQ m) := by
  apply memQ_row
  rcases Nat.eq_or_lt_of_le h1 with he | hlt
  · left
    rw [← he, ZMod.natCast_self, neg_zero]
  · right
    rw [val_neg_natCast_reduce (by omega) (by omega)]
    omega

private theorem memQ_rowRun2 (hm : 4 ≤ m) {k : Nat} (h1 : m ≤ k)
    (h2 : k ≤ 2 * m - 4) :
    memQ (((k : ZMod m) + 3, -1) : TerminalQ m) := by
  apply memQ_row
  right
  have hcast : ((k : ZMod m) + 3 : ZMod m) =
      ((k - m + 3 : Nat) : ZMod m) := by
    rw [natCast_reduce h1]; push_cast; ring
  rw [hcast, val_natCast (by omega)]
  omega

private theorem memQ_zeroRow : memQ ((0, -1) : TerminalQ m) :=
  memQ_row (Or.inl rfl)

private theorem memS_colRun (hm : 4 ≤ m) {k : Nat} (h1 : 3 ≤ k)
    (h2 : k ≤ m) : memS ((2, -(k : ZMod m)) : TerminalQ m) := by
  apply memS_col
  rcases Nat.eq_or_lt_of_le h2 with he | hlt
  · rw [he, ZMod.natCast_self, neg_zero, val0]
    omega
  · rw [val_neg_natCast (by omega) hlt]
    omega

private theorem memS_colRun2 (hm : 4 ≤ m) {k : Nat} (hk : k ≤ m - 3) :
    memS ((2, (k : ZMod m)) : TerminalQ m) :=
  memS_col (by rw [val_natCast (by omega)]; omega)

end RunMembers

/-! ## The rank-step (traversal) lemmas -/

section StepLemmas

variable {m : Nat} [NeZero m]

/-- `ρ₀` advances the color-0 zigzag by one rank. -/
theorem rho_seamPoint0 (hm : 4 ≤ m) (n : SeamLabel m) :
    rho 0 (seamPoint0 m n) = seamPoint0 m (seamSucc m n) := by
  have hlt := n.isLt
  unfold seamPoint0
  by_cases hF : n.val = 2 * m - 1
  · -- wrap: (1, 0) ∈ Q kicks back to (0, 0)
    rw [seamSucc_val_last hF, seamPoint0Nat_last hm hF,
      seamPoint0Nat_anti hm (by omega : (0 : Nat) ≤ m - 2),
      rho_zero_of_memQ hm memQ_one, Prod.mk.injEq]
    constructor <;> norm_num
  rw [seamSucc_val_of_lt (by omega)]
  by_cases hA : n.val ≤ m - 3
  · -- P anti-diagonal run
    rw [seamPoint0Nat_anti hm (by omega), seamPoint0Nat_anti hm (by omega),
      rho_zero_of_memP (memP_run0 hm hA), Prod.mk.injEq]
    constructor <;> (push_cast; ring)
  by_cases hB : n.val = m - 2
  · -- Q pivot (2, −2) hops to (1, −2)
    rw [seamPoint0Nat_anti hm (by omega), hB, pt_anti_end hm,
      rho_zero_of_memQ hm memQ_two,
      seamPoint0Nat_mid hm (show m - 2 + 1 = m - 1 from by omega),
      Prod.mk.injEq]
    exact ⟨by norm_num, rfl⟩
  by_cases hC : n.val = m - 1
  · -- (1, −2) ∈ P hops to the Q row at (0, −1)
    rw [seamPoint0Nat_mid hm hC, rho_zero_of_memP memP_one, hC,
      seamPoint0Nat_row hm (by omega) (by omega),
      show m - 1 + 1 = m from by omega, Prod.mk.injEq]
    constructor
    · rw [ZMod.natCast_self, neg_zero]; norm_num
    · norm_num
  by_cases hE : n.val = 2 * m - 2
  · -- P pivot (2, −1) hops to (1, 0)
    rw [seamPoint0Nat_rowEnd hm hE, rho_zero_of_memP memP_two, hE,
      seamPoint0Nat_last hm (show 2 * m - 2 + 1 = 2 * m - 1 from by omega),
      Prod.mk.injEq]
    constructor <;> norm_num
  · -- Q row run
    rw [seamPoint0Nat_row hm (by omega) (by omega),
      seamPoint0Nat_row hm (by omega) (by omega),
      rho_zero_of_memQ hm (memQ_rowRun hm (by omega) (by omega)),
      Prod.mk.injEq]
    exact ⟨by push_cast; ring, rfl⟩

/-- `ρ₁` advances the color-1 zigzag by one rank. -/
theorem rho_seamPoint1 (hm : 4 ≤ m) (n : SeamLabel m) :
    rho 1 (seamPoint1 m n) = seamPoint1 m (seamSucc m n) := by
  have hlt := n.isLt
  unfold seamPoint1
  by_cases hI : n.val = 2 * m - 1
  · -- wrap: (−1, 1) ∈ P kicks back to (0, 0)
    rw [seamSucc_val_last hI,
      seamPoint1Nat_anti hm (by omega) (by omega),
      rho_one_of_memP (memP_runAnti hm (by omega) (by omega)),
      seamPoint1Nat_zero hm rfl, hI, Prod.mk.injEq]
    constructor
    · rw [natCast_reduce (by omega),
        show 2 * m - 1 - m = m - 1 from by omega, natCast_m_sub_one hm]
      ring
    · rw [natCast_reduce (by omega),
        show 2 * m - 1 - m = m - 1 from by omega, natCast_m_sub_one hm]
      ring
  rw [seamSucc_val_of_lt (by omega)]
  by_cases h0 : n.val = 0
  · rw [seamPoint1Nat_zero hm h0, rho_one_of_memP memP_zero,
      seamPoint1Nat_one hm (show n.val + 1 = 1 from by omega),
      Prod.mk.injEq]
    constructor <;> norm_num
  by_cases h1 : n.val = 1
  · rw [seamPoint1Nat_one hm h1, rho_one_of_memS hm memS_one,
      seamPoint1Nat_two hm (show n.val + 1 = 2 from by omega),
      Prod.mk.injEq]
    constructor
    · rfl
    · norm_num
  by_cases h2 : n.val = 2
  · rw [seamPoint1Nat_two hm h2, rho_one_of_memP memP_one, h2,
      seamPoint1Nat_col hm (by omega) (by omega), Prod.mk.injEq]
    constructor
    · norm_num
    · push_cast; ring
  by_cases hcol : n.val ≤ m - 1
  · -- S column run
    rw [seamPoint1Nat_col hm (by omega) (by omega),
      seamPoint1Nat_col hm (by omega) (by omega),
      rho_one_of_memS hm (memS_colRun hm (by omega) (by omega)),
      Prod.mk.injEq]
    exact ⟨rfl, by push_cast; ring⟩
  by_cases hm0 : n.val = m
  · -- bottom of the S column hops to (2, −1)
    rw [seamPoint1Nat_col hm (by omega) (by omega),
      rho_one_of_memS hm (memS_colRun hm (by omega) (by omega)),
      seamPoint1Nat_colEnd hm (show n.val + 1 = m + 1 from by omega),
      hm0, Prod.mk.injEq]
    constructor
    · rfl
    · rw [ZMod.natCast_self]; ring
  by_cases hm1 : n.val = m + 1
  · rw [seamPoint1Nat_colEnd hm hm1, rho_one_of_memP memP_two,
      seamPoint1Nat_hop hm (show n.val + 1 = m + 2 from by omega),
      Prod.mk.injEq]
    constructor <;> norm_num
  by_cases hm2 : n.val = m + 2
  · rw [seamPoint1Nat_hop hm hm2, rho_one_of_memS hm memS_three, hm2,
      seamPoint1Nat_anti hm (by omega) (by omega),
      show m + 2 + 1 = m + 3 from by omega, natCast_reduce (by omega),
      show m + 3 - m = 3 from by omega, ← three_eq_natCast,
      Prod.mk.injEq]
    constructor
    · rfl
    · ring
  · -- P anti-diagonal run
    rw [seamPoint1Nat_anti hm (by omega) (by omega),
      seamPoint1Nat_anti hm (by omega) (by omega),
      rho_one_of_memP (memP_runAnti hm (by omega) (by omega)),
      Prod.mk.injEq]
    constructor <;> (push_cast; ring)

/-- `ρ₂` advances the color-2 zigzag by one rank. -/
theorem rho_seamPoint2 (hm : 4 ≤ m) (n : SeamLabel m) :
    rho 2 (seamPoint2 m n) = seamPoint2 m (seamSucc m n) := by
  have hlt := n.isLt
  unfold seamPoint2
  by_cases hG : n.val = 2 * m - 1
  · -- wrap: (1, 0) ∈ Q kicks back to (2, 0)
    rw [seamSucc_val_last hG, seamPoint2Nat_last hm hG,
      seamPoint2Nat_col hm (by omega : (0 : Nat) ≤ m - 2),
      rho_two_of_memQ hm memQ_one, Prod.mk.injEq]
    constructor <;> norm_num
  rw [seamSucc_val_of_lt (by omega)]
  by_cases hA : n.val ≤ m - 3
  · -- S column run
    rw [seamPoint2Nat_col hm (by omega), seamPoint2Nat_col hm (by omega),
      rho_two_of_memS hm (memS_colRun2 hm hA), Prod.mk.injEq]
    exact ⟨rfl, by push_cast; ring⟩
  by_cases hB : n.val = m - 2
  · -- Q pivot (2, −2) hops to (3, −2)
    rw [seamPoint2Nat_col hm (by omega), hB, natCast_m_sub_two hm,
      rho_two_of_memQ hm memQ_two,
      seamPoint2Nat_hop hm (show m - 2 + 1 = m - 1 from by omega),
      Prod.mk.injEq]
    exact ⟨by norm_num, rfl⟩
  by_cases hC : n.val = m - 1
  · -- (3, −2) ∈ S hops to the Q row at (3, −1)
    rw [seamPoint2Nat_hop hm hC, rho_two_of_memS hm memS_three, hC,
      seamPoint2Nat_row hm (by omega) (by omega),
      show m - 1 + 1 = m from by omega, ZMod.natCast_self,
      Prod.mk.injEq]
    constructor
    · ring
    · ring
  by_cases hE : n.val = 2 * m - 3
  · -- end of the Q row (0, −1) hops to (1, −1)
    rw [seamPoint2Nat_rowZero hm hE, rho_two_of_memQ hm memQ_zeroRow,
      seamPoint2Nat_preLast hm
        (show n.val + 1 = 2 * m - 2 from by omega),
      Prod.mk.injEq]
    constructor <;> norm_num
  by_cases hF : n.val = 2 * m - 2
  · rw [seamPoint2Nat_preLast hm hF, rho_two_of_memS hm memS_one,
      seamPoint2Nat_last hm (show n.val + 1 = 2 * m - 1 from by omega),
      Prod.mk.injEq]
    constructor
    · rfl
    · ring
  · -- Q row run
    rw [seamPoint2Nat_row hm (by omega) (by omega),
      seamPoint2Nat_row hm (by omega) (by omega),
      rho_two_of_memQ hm (memQ_rowRun2 hm (by omega) (by omega)),
      Prod.mk.injEq]
    exact ⟨by push_cast; ring, rfl⟩

end StepLemmas

/-! ## Inverse ranks and injectivity of the zigzag enumerations -/

/-- Inverse rank for the color-0 zigzag. -/
def seamRank0 (m : Nat) (w : TerminalQ m) : Nat :=
  if w = (1, -2) then m - 1
  else if w = (2, -1) then 2 * m - 2
  else if w = (1, 0) then 2 * m - 1
  else if w.2 = -1 then m + (m - w.1.val) % m
  else w.2.val

/-- Inverse rank for the color-1 zigzag. -/
def seamRank1 (m : Nat) (w : TerminalQ m) : Nat :=
  if w = (0, 0) then 0
  else if w = (1, -1) then 1
  else if w = (1, -2) then 2
  else if w = (2, -1) then m + 1
  else if w = (3, -2) then m + 2
  else if w.1 = 2 then m - w.2.val
  else m + w.1.val

/-- Inverse rank for the color-2 zigzag. -/
def seamRank2 (m : Nat) (w : TerminalQ m) : Nat :=
  if w = (3, -2) then m - 1
  else if w = (0, -1) then 2 * m - 3
  else if w = (1, -1) then 2 * m - 2
  else if w = (1, 0) then 2 * m - 1
  else if w.1 = 2 then w.2.val
  else m + w.1.val - 3

section RankLemmas

variable {m : Nat} [NeZero m]

private theorem seamRank0_seamPoint0Nat (hm : 4 ≤ m) {k : Nat}
    (hk : k ≤ 2 * m - 1) : seamRank0 m (seamPoint0Nat m k) = k := by
  by_cases hA : k ≤ m - 2
  · rw [seamPoint0Nat_anti hm hA]
    rcases Nat.eq_zero_or_pos k with h0 | h1
    · subst h0
      simp only [Nat.cast_zero, neg_zero]
      unfold seamRank0
      rw [if_neg (pair_ne_fst (by rw [val0, val1 hm]; omega)),
        if_neg (pair_ne_fst (by rw [val0, val2 hm]; omega)),
        if_neg (pair_ne_fst (by rw [val0, val1 hm]; omega)),
        if_neg (ne_of_val_ne (a := (0 : ZMod m)) (b := (-1 : ZMod m))
          (by rw [val0, valn1 hm]; omega))]
      exact val0
    · have hv1 : (-(k : ZMod m)).val = m - k :=
        val_neg_natCast (by omega) (by omega)
      have hv2 : ((k : ZMod m)).val = k := val_natCast (by omega)
      unfold seamRank0
      rw [if_neg (pair_ne_fst (by rw [hv1, val1 hm]; omega)),
        if_neg (pair_ne_snd (by rw [hv2, valn1 hm]; omega)),
        if_neg (pair_ne_fst (by rw [hv1, val1 hm]; omega)),
        if_neg (ne_of_val_ne (a := ((k : ZMod m))) (b := (-1 : ZMod m))
          (by rw [hv2, valn1 hm]; omega))]
      exact hv2
  by_cases hB : k = m - 1
  · rw [seamPoint0Nat_mid hm hB]
    unfold seamRank0
    rw [if_pos rfl]
    omega
  by_cases hC : k ≤ 2 * m - 3
  · rw [seamPoint0Nat_row hm (by omega) (by omega)]
    rcases Nat.eq_or_lt_of_le (show m ≤ k from by omega) with he | hlt
    · rw [← he, neg_natCast_self]
      unfold seamRank0
      rw [if_neg (pair_ne_fst (by rw [val0, val1 hm]; omega)),
        if_neg (pair_ne_fst (by rw [val0, val2 hm]; omega)),
        if_neg (pair_ne_fst (by rw [val0, val1 hm]; omega)),
        if_pos rfl, val0, Nat.sub_zero, Nat.mod_self]
      omega
    · have hv1 : (-(k : ZMod m)).val = 2 * m - k :=
        val_neg_natCast_reduce (by omega) (by omega)
      unfold seamRank0
      rw [if_neg (pair_ne_snd (by rw [valn1 hm, valn2 hm]; omega)),
        if_neg (pair_ne_fst (by rw [hv1, val2 hm]; omega)),
        if_neg (pair_ne_snd (by rw [valn1 hm, val0]; omega)),
        if_pos rfl, hv1, show m - (2 * m - k) = k - m from by omega,
        Nat.mod_eq_of_lt (by omega)]
      omega
  by_cases hD : k = 2 * m - 2
  · rw [seamPoint0Nat_rowEnd hm hD]
    unfold seamRank0
    rw [if_neg (pair_ne_fst (by rw [val2 hm, val1 hm]; omega)),
      if_pos rfl]
    omega
  · rw [seamPoint0Nat_last hm (by omega)]
    unfold seamRank0
    rw [if_neg (pair_ne_snd (by rw [val0, valn2 hm]; omega)),
      if_neg (pair_ne_fst (by rw [val1 hm, val2 hm]; omega)),
      if_pos rfl]
    omega

private theorem seamRank1_seamPoint1Nat (hm : 4 ≤ m) {k : Nat}
    (hk : k ≤ 2 * m - 1) : seamRank1 m (seamPoint1Nat m k) = k := by
  by_cases h0 : k = 0
  · rw [seamPoint1Nat_zero hm h0]
    unfold seamRank1
    rw [if_pos rfl]
    omega
  by_cases h1 : k = 1
  · rw [seamPoint1Nat_one hm h1]
    unfold seamRank1
    rw [if_neg (pair_ne_fst (by rw [val1 hm, val0]; omega)), if_pos rfl]
    omega
  by_cases h2 : k = 2
  · rw [seamPoint1Nat_two hm h2]
    unfold seamRank1
    rw [if_neg (pair_ne_fst (by rw [val1 hm, val0]; omega)),
      if_neg (pair_ne_snd (by rw [valn2 hm, valn1 hm]; omega)),
      if_pos rfl]
    omega
  by_cases hcol : k ≤ m - 1
  · rw [seamPoint1Nat_col hm (by omega) (by omega)]
    have hv : (-(k : ZMod m)).val = m - k :=
      val_neg_natCast (by omega) (by omega)
    unfold seamRank1
    rw [if_neg (pair_ne_fst (by rw [val2 hm, val0]; omega)),
      if_neg (pair_ne_fst (by rw [val2 hm, val1 hm]; omega)),
      if_neg (pair_ne_fst (by rw [val2 hm, val1 hm]; omega)),
      if_neg (pair_ne_snd (by rw [hv, valn1 hm]; omega)),
      if_neg (pair_ne_fst (by rw [val2 hm, val3 hm]; omega)),
      if_pos rfl, hv]
    omega
  by_cases hm0 : k = m
  · rw [seamPoint1Nat_col hm (by omega) (by omega), hm0,
      neg_natCast_self]
    unfold seamRank1
    rw [if_neg (pair_ne_fst (by rw [val2 hm, val0]; omega)),
      if_neg (pair_ne_fst (by rw [val2 hm, val1 hm]; omega)),
      if_neg (pair_ne_fst (by rw [val2 hm, val1 hm]; omega)),
      if_neg (pair_ne_snd (by rw [val0, valn1 hm]; omega)),
      if_neg (pair_ne_fst (by rw [val2 hm, val3 hm]; omega)),
      if_pos rfl, val0]
    omega
  by_cases hm1 : k = m + 1
  · rw [seamPoint1Nat_colEnd hm hm1]
    unfold seamRank1
    rw [if_neg (pair_ne_fst (by rw [val2 hm, val0]; omega)),
      if_neg (pair_ne_fst (by rw [val2 hm, val1 hm]; omega)),
      if_neg (pair_ne_fst (by rw [val2 hm, val1 hm]; omega)),
      if_pos rfl]
    omega
  by_cases hm2 : k = m + 2
  · rw [seamPoint1Nat_hop hm hm2]
    unfold seamRank1
    rw [if_neg (pair_ne_fst (by rw [val3 hm, val0]; omega)),
      if_neg (pair_ne_fst (by rw [val3 hm, val1 hm]; omega)),
      if_neg (pair_ne_fst (by rw [val3 hm, val1 hm]; omega)),
      if_neg (pair_ne_fst (by rw [val3 hm, val2 hm]; omega)),
      if_pos rfl]
    omega
  · rw [seamPoint1Nat_anti hm (by omega) (by omega)]
    have hva : ((k : ZMod m)).val = k - m :=
      val_natCast_reduce (by omega) (by omega)
    have hvb : (-(k : ZMod m)).val = 2 * m - k :=
      val_neg_natCast_reduce (by omega) (by omega)
    unfold seamRank1
    rw [if_neg (pair_ne_fst (by rw [hva, val0]; omega)),
      if_neg (pair_ne_fst (by rw [hva, val1 hm]; omega)),
      if_neg (pair_ne_fst (by rw [hva, val1 hm]; omega)),
      if_neg (pair_ne_fst (by rw [hva, val2 hm]; omega)),
      if_neg (pair_ne_snd (by rw [hvb, valn2 hm]; omega)),
      if_neg (ne_of_val_ne (a := ((k : ZMod m))) (b := (2 : ZMod m))
        (by rw [hva, val2 hm]; omega)),
      hva]
    omega

private theorem seamRank2_seamPoint2Nat (hm : 4 ≤ m) {k : Nat}
    (hk : k ≤ 2 * m - 1) : seamRank2 m (seamPoint2Nat m k) = k := by
  by_cases hA : k ≤ m - 2
  · rw [seamPoint2Nat_col hm hA]
    have hv : ((k : ZMod m)).val = k := val_natCast (by omega)
    unfold seamRank2
    rw [if_neg (pair_ne_fst (by rw [val2 hm, val3 hm]; omega)),
      if_neg (pair_ne_fst (by rw [val2 hm, val0]; omega)),
      if_neg (pair_ne_fst (by rw [val2 hm, val1 hm]; omega)),
      if_neg (pair_ne_fst (by rw [val2 hm, val1 hm]; omega)),
      if_pos rfl]
    exact hv
  by_cases hB : k = m - 1
  · rw [seamPoint2Nat_hop hm hB]
    unfold seamRank2
    rw [if_pos rfl]
    omega
  by_cases hC : k ≤ 2 * m - 4
  · rw [seamPoint2Nat_row hm (by omega) (by omega)]
    have hcast : ((k : ZMod m) + 3 : ZMod m) =
        ((k - m + 3 : Nat) : ZMod m) := by
      rw [natCast_reduce (by omega)]; push_cast; ring
    rw [hcast]
    have hv : ((k - m + 3 : Nat) : ZMod m).val = k - m + 3 :=
      val_natCast (by omega)
    unfold seamRank2
    rw [if_neg (pair_ne_snd (by rw [valn1 hm, valn2 hm]; omega)),
      if_neg (pair_ne_fst (by rw [hv, val0]; omega)),
      if_neg (pair_ne_fst (by rw [hv, val1 hm]; omega)),
      if_neg (pair_ne_snd (by rw [valn1 hm, val0]; omega)),
      if_neg (ne_of_val_ne (a := ((k - m + 3 : Nat) : ZMod m))
        (b := (2 : ZMod m)) (by rw [hv, val2 hm]; omega)),
      hv]
    omega
  by_cases hD : k = 2 * m - 3
  · rw [seamPoint2Nat_rowZero hm hD]
    unfold seamRank2
    rw [if_neg (pair_ne_fst (by rw [val0, val3 hm]; omega)), if_pos rfl]
    omega
  by_cases hE : k = 2 * m - 2
  · rw [seamPoint2Nat_preLast hm hE]
    unfold seamRank2
    rw [if_neg (pair_ne_fst (by rw [val1 hm, val3 hm]; omega)),
      if_neg (pair_ne_fst (by rw [val1 hm, val0]; omega)),
      if_pos rfl]
    omega
  · rw [seamPoint2Nat_last hm (by omega)]
    unfold seamRank2
    rw [if_neg (pair_ne_fst (by rw [val1 hm, val3 hm]; omega)),
      if_neg (pair_ne_fst (by rw [val1 hm, val0]; omega)),
      if_neg (pair_ne_snd (by rw [val0, valn1 hm]; omega)),
      if_pos rfl]
    omega

/-- `seamRank0` inverts `seamPoint0`. -/
theorem seamRank0_seamPoint0 (hm : 4 ≤ m) (n : SeamLabel m) :
    seamRank0 m (seamPoint0 m n) = n.val :=
  seamRank0_seamPoint0Nat hm (by have := n.isLt; omega)

/-- `seamRank1` inverts `seamPoint1`. -/
theorem seamRank1_seamPoint1 (hm : 4 ≤ m) (n : SeamLabel m) :
    seamRank1 m (seamPoint1 m n) = n.val :=
  seamRank1_seamPoint1Nat hm (by have := n.isLt; omega)

/-- `seamRank2` inverts `seamPoint2`. -/
theorem seamRank2_seamPoint2 (hm : 4 ≤ m) (n : SeamLabel m) :
    seamRank2 m (seamPoint2 m n) = n.val :=
  seamRank2_seamPoint2Nat hm (by have := n.isLt; omega)

theorem seamPoint0_injective (hm : 4 ≤ m) :
    Function.Injective (seamPoint0 m) := by
  intro a b h
  have ha := seamRank0_seamPoint0 hm a
  have hb := seamRank0_seamPoint0 hm b
  apply Fin.ext
  rw [← ha, ← hb, h]

theorem seamPoint1_injective (hm : 4 ≤ m) :
    Function.Injective (seamPoint1 m) := by
  intro a b h
  have ha := seamRank1_seamPoint1 hm a
  have hb := seamRank1_seamPoint1 hm b
  apply Fin.ext
  rw [← ha, ← hb, h]

theorem seamPoint2_injective (hm : 4 ≤ m) :
    Function.Injective (seamPoint2 m) := by
  intro a b h
  have ha := seamRank2_seamPoint2 hm a
  have hb := seamRank2_seamPoint2 hm b
  apply Fin.ext
  rw [← ha, ← hb, h]

end RankLemmas

/-! ## Unified per-color packaging -/

/-- Per-color zigzag enumeration: `c = 0 ↦ P ∪ Q`, `c = 1 ↦ P ∪ S`,
`c = 2 ↦ Q ∪ S`. -/
def seamPoint (m : Nat) : Fin 3 → SeamLabel m → TerminalQ m
  | 0 => seamPoint0 m
  | 1 => seamPoint1 m
  | 2 => seamPoint2 m

/-- The union of the two rails moved by color `c`. -/
def activePred {m : Nat} : Fin 3 → TerminalQ m → Prop
  | 0, w => memP w ∨ memQ w
  | 1, w => memP w ∨ memS w
  | 2, w => memQ w ∨ memS w

private theorem fin3_cases (c : Fin 3) : c = 0 ∨ c = 1 ∨ c = 2 := by
  revert c; decide

section ActiveSet

variable {m : Nat} [NeZero m]

/-- Unified rank-step lemma: `rho c` advances the color-`c` zigzag. -/
theorem rho_seamPoint (hm : 4 ≤ m) (c : Fin 3) (n : SeamLabel m) :
    rho c (seamPoint m c n) = seamPoint m c (seamSucc m n) := by
  rcases fin3_cases c with rfl | rfl | rfl
  · exact rho_seamPoint0 hm n
  · exact rho_seamPoint1 hm n
  · exact rho_seamPoint2 hm n

/-- Unified injectivity of the zigzag enumerations. -/
theorem seamPoint_injective (hm : 4 ≤ m) (c : Fin 3) :
    Function.Injective (seamPoint m c) := by
  rcases fin3_cases c with rfl | rfl | rfl
  · exact seamPoint0_injective hm
  · exact seamPoint1_injective hm
  · exact seamPoint2_injective hm

private theorem one_ne_zero' (hm : 4 ≤ m) : (1 : ZMod m) ≠ 0 :=
  ne_of_val_ne (by rw [val1 hm, val0]; omega)

private theorem rho_zero_eq_of_off (hm : 4 ≤ m) {w : TerminalQ m}
    (h : ¬(memP w ∨ memQ w)) : rho 0 w = w := by
  rw [not_or] at h
  by_cases hs : memS w
  · exact rho_zero_of_memS hm hs
  · exact rho_of_off h.1 h.2 hs 0

private theorem rho_one_eq_of_off (hm : 4 ≤ m) {w : TerminalQ m}
    (h : ¬(memP w ∨ memS w)) : rho 1 w = w := by
  rw [not_or] at h
  by_cases hq : memQ w
  · exact rho_one_of_memQ hm hq
  · exact rho_of_off h.1 hq h.2 1

private theorem rho_two_eq_of_off (hm : 4 ≤ m) {w : TerminalQ m}
    (h : ¬(memQ w ∨ memS w)) : rho 2 w = w := by
  rw [not_or] at h
  by_cases hp : memP w
  · exact rho_two_of_memP hp
  · exact rho_of_off hp h.1 h.2 2

/-- `ρ₀` moves a cell iff the cell lies on `P ∪ Q`. -/
theorem rho_zero_ne_iff (hm : 4 ≤ m) (w : TerminalQ m) :
    rho 0 w ≠ w ↔ memP w ∨ memQ w := by
  constructor
  · intro hne
    by_contra hoff
    exact hne (rho_zero_eq_of_off hm hoff)
  · obtain ⟨a, b⟩ := w
    rintro (hp | hq) he
    · rw [rho_zero_of_memP hp] at he
      have hfst : a - 1 = a := congrArg Prod.fst he
      exact one_ne_zero' hm (by linear_combination -hfst)
    · rw [rho_zero_of_memQ hm hq] at he
      have hfst : a - 1 = a := congrArg Prod.fst he
      exact one_ne_zero' hm (by linear_combination -hfst)

/-- `ρ₁` moves a cell iff the cell lies on `P ∪ S`. -/
theorem rho_one_ne_iff (hm : 4 ≤ m) (w : TerminalQ m) :
    rho 1 w ≠ w ↔ memP w ∨ memS w := by
  constructor
  · intro hne
    by_contra hoff
    exact hne (rho_one_eq_of_off hm hoff)
  · obtain ⟨a, b⟩ := w
    rintro (hp | hs) he
    · rw [rho_one_of_memP hp] at he
      have hfst : a + 1 = a := congrArg Prod.fst he
      exact one_ne_zero' hm (by linear_combination hfst)
    · rw [rho_one_of_memS hm hs] at he
      have hsnd : b - 1 = b := congrArg Prod.snd he
      exact one_ne_zero' hm (by linear_combination -hsnd)

/-- `ρ₂` moves a cell iff the cell lies on `Q ∪ S`. -/
theorem rho_two_ne_iff (hm : 4 ≤ m) (w : TerminalQ m) :
    rho 2 w ≠ w ↔ memQ w ∨ memS w := by
  constructor
  · intro hne
    by_contra hoff
    exact hne (rho_two_eq_of_off hm hoff)
  · obtain ⟨a, b⟩ := w
    rintro (hq | hs) he
    · rw [rho_two_of_memQ hm hq] at he
      have hfst : a + 1 = a := congrArg Prod.fst he
      exact one_ne_zero' hm (by linear_combination hfst)
    · rw [rho_two_of_memS hm hs] at he
      have hsnd : b + 1 = b := congrArg Prod.snd he
      exact one_ne_zero' hm (by linear_combination hsnd)

/-- Active-set lemma, predicate form: `ρ_c` moves a cell iff the cell lies
on one of the two rails involving color `c`. -/
theorem rho_ne_self_iff (hm : 4 ≤ m) (c : Fin 3) (w : TerminalQ m) :
    rho c w ≠ w ↔ activePred c w := by
  rcases fin3_cases c with rfl | rfl | rfl
  · exact rho_zero_ne_iff hm w
  · exact rho_one_ne_iff hm w
  · exact rho_two_ne_iff hm w

theorem rho_eq_of_not_active (hm : 4 ≤ m) (c : Fin 3) {w : TerminalQ m}
    (h : ¬activePred c w) : rho c w = w := by
  by_contra hne
  exact h ((rho_ne_self_iff hm c w).mp hne)

/-- Every zigzag point is active for its color. -/
theorem seamPoint_active (hm : 4 ≤ m) (c : Fin 3) (n : SeamLabel m) :
    activePred c (seamPoint m c n) := by
  by_contra hna
  have h1 := rho_eq_of_not_active hm c hna
  rw [rho_seamPoint hm c n] at h1
  exact seamSucc_ne n (seamPoint_injective hm c h1)

end ActiveSet

/-! ## The active rails are exactly the zigzag ranges -/

section RangeLemmas

variable {m : Nat} [NeZero m]

private theorem exists_seamPoint0_of_active (hm : 4 ≤ m)
    {w : TerminalQ m} (h : memP w ∨ memQ w) :
    ∃ n : SeamLabel m, seamPoint0 m n = w := by
  rcases h with hp | hq
  · rcases hp with h | ⟨hsum, hx⟩ | h | h
    · refine ⟨⟨0, by omega⟩, ?_⟩
      change seamPoint0Nat m 0 = w
      rw [seamPoint0Nat_anti hm (show (0 : Nat) ≤ m - 2 from by omega), h]
      simp only [Nat.cast_zero, neg_zero]
    · have hlt := ZMod.val_lt w.1
      refine ⟨⟨m - w.1.val, by omega⟩, ?_⟩
      change seamPoint0Nat m (m - w.1.val) = w
      rw [seamPoint0Nat_anti hm (by omega)]
      have h1 : ((m - w.1.val : Nat) : ZMod m) = -w.1 := by
        rw [natCast_sub_eq_neg (by omega), ZMod.natCast_zmod_val]
      have h2 : w.2 = -w.1 := by linear_combination hsum
      rw [h1, neg_neg, ← h2]
    · refine ⟨⟨m - 1, by omega⟩, ?_⟩
      change seamPoint0Nat m (m - 1) = w
      rw [seamPoint0Nat_mid hm rfl, h]
    · refine ⟨⟨2 * m - 2, by omega⟩, ?_⟩
      change seamPoint0Nat m (2 * m - 2) = w
      rw [seamPoint0Nat_rowEnd hm rfl, h]
  · rcases hq with ⟨h1, h2⟩ | h | h
    · rcases h2 with h2 | h2
      · refine ⟨⟨m, by omega⟩, ?_⟩
        change seamPoint0Nat m m = w
        rw [seamPoint0Nat_row hm (by omega) (by omega), neg_natCast_self]
        exact (Prod.ext_iff.mpr ⟨h2, h1⟩).symm
      · have hlt := ZMod.val_lt w.1
        refine ⟨⟨2 * m - w.1.val, by omega⟩, ?_⟩
        change seamPoint0Nat m (2 * m - w.1.val) = w
        rw [seamPoint0Nat_row hm (by omega) (by omega)]
        have hc : ((2 * m - w.1.val : Nat) : ZMod m) = -w.1 := by
          rw [natCast_reduce (by omega),
            show 2 * m - w.1.val - m = m - w.1.val from by omega,
            natCast_sub_eq_neg (by omega), ZMod.natCast_zmod_val]
        rw [hc, neg_neg]
        symm
        exact Prod.ext_iff.mpr ⟨rfl, h1⟩
    · refine ⟨⟨2 * m - 1, by omega⟩, ?_⟩
      change seamPoint0Nat m (2 * m - 1) = w
      rw [seamPoint0Nat_last hm rfl, h]
    · refine ⟨⟨m - 2, by omega⟩, ?_⟩
      change seamPoint0Nat m (m - 2) = w
      rw [seamPoint0Nat_anti hm (by omega), pt_anti_end hm, h]

private theorem exists_seamPoint1_of_active (hm : 4 ≤ m)
    {w : TerminalQ m} (h : memP w ∨ memS w) :
    ∃ n : SeamLabel m, seamPoint1 m n = w := by
  rcases h with hp | hs
  · rcases hp with h | ⟨hsum, hx⟩ | h | h
    · refine ⟨⟨0, by omega⟩, ?_⟩
      change seamPoint1Nat m 0 = w
      rw [seamPoint1Nat_zero hm rfl, h]
    · have hlt := ZMod.val_lt w.1
      refine ⟨⟨m + w.1.val, by omega⟩, ?_⟩
      change seamPoint1Nat m (m + w.1.val) = w
      rw [seamPoint1Nat_anti hm (by omega) (by omega)]
      have hc : ((m + w.1.val : Nat) : ZMod m) = w.1 := by
        rw [natCast_reduce (by omega),
          show m + w.1.val - m = w.1.val from by omega,
          ZMod.natCast_zmod_val]
      have h2 : w.2 = -w.1 := by linear_combination hsum
      rw [hc, ← h2]
    · refine ⟨⟨2, by omega⟩, ?_⟩
      change seamPoint1Nat m 2 = w
      rw [seamPoint1Nat_two hm rfl, h]
    · refine ⟨⟨m + 1, by omega⟩, ?_⟩
      change seamPoint1Nat m (m + 1) = w
      rw [seamPoint1Nat_colEnd hm rfl, h]
  · rcases hs with ⟨h1, h2⟩ | h | h
    · rcases Nat.eq_zero_or_pos w.2.val with hv0 | hv1
      · refine ⟨⟨m, by omega⟩, ?_⟩
        change seamPoint1Nat m m = w
        rw [seamPoint1Nat_col hm (by omega) (by omega), neg_natCast_self]
        have hw2 : (0 : ZMod m) = w.2 :=
          (val_inj (by rw [hv0, val0])).symm
        exact (Prod.ext_iff.mpr ⟨h1, hw2.symm⟩).symm
      · refine ⟨⟨m - w.2.val, by omega⟩, ?_⟩
        change seamPoint1Nat m (m - w.2.val) = w
        rw [seamPoint1Nat_col hm (by omega) (by omega)]
        have hc : ((m - w.2.val : Nat) : ZMod m) = -w.2 := by
          rw [natCast_sub_eq_neg (by omega), ZMod.natCast_zmod_val]
        rw [hc, neg_neg]
        symm
        exact Prod.ext_iff.mpr ⟨h1, rfl⟩
    · refine ⟨⟨1, by omega⟩, ?_⟩
      change seamPoint1Nat m 1 = w
      rw [seamPoint1Nat_one hm rfl, h]
    · refine ⟨⟨m + 2, by omega⟩, ?_⟩
      change seamPoint1Nat m (m + 2) = w
      rw [seamPoint1Nat_hop hm rfl, h]

private theorem exists_seamPoint2_of_active (hm : 4 ≤ m)
    {w : TerminalQ m} (h : memQ w ∨ memS w) :
    ∃ n : SeamLabel m, seamPoint2 m n = w := by
  rcases h with hq | hs
  · rcases hq with ⟨h1, h2⟩ | h | h
    · rcases h2 with h2 | h2
      · refine ⟨⟨2 * m - 3, by omega⟩, ?_⟩
        change seamPoint2Nat m (2 * m - 3) = w
        rw [seamPoint2Nat_rowZero hm rfl]
        exact (Prod.ext_iff.mpr ⟨h2, h1⟩).symm
      · have hlt := ZMod.val_lt w.1
        refine ⟨⟨m + w.1.val - 3, by omega⟩, ?_⟩
        change seamPoint2Nat m (m + w.1.val - 3) = w
        rw [seamPoint2Nat_row hm (by omega) (by omega)]
        have hc : ((m + w.1.val - 3 : Nat) : ZMod m) + 3 = w.1 := by
          rw [natCast_reduce (by omega),
            show m + w.1.val - 3 - m = w.1.val - 3 from by omega,
            three_eq_natCast]
          calc ((w.1.val - 3 : Nat) : ZMod m) + ((3 : Nat) : ZMod m)
              = ((w.1.val - 3 + 3 : Nat) : ZMod m) := by push_cast; ring
            _ = ((w.1.val : Nat) : ZMod m) := by
                rw [show w.1.val - 3 + 3 = w.1.val from by omega]
            _ = w.1 := ZMod.natCast_zmod_val w.1
        rw [hc]
        symm
        exact Prod.ext_iff.mpr ⟨rfl, h1⟩
    · refine ⟨⟨2 * m - 1, by omega⟩, ?_⟩
      change seamPoint2Nat m (2 * m - 1) = w
      rw [seamPoint2Nat_last hm rfl, h]
    · refine ⟨⟨m - 2, by omega⟩, ?_⟩
      change seamPoint2Nat m (m - 2) = w
      rw [seamPoint2Nat_col hm (by omega), natCast_m_sub_two hm, h]
  · rcases hs with ⟨h1, h2⟩ | h | h
    · refine ⟨⟨w.2.val, by have := ZMod.val_lt w.2; omega⟩, ?_⟩
      change seamPoint2Nat m w.2.val = w
      rw [seamPoint2Nat_col hm (by omega), ZMod.natCast_zmod_val]
      symm
      exact Prod.ext_iff.mpr ⟨h1, rfl⟩
    · refine ⟨⟨2 * m - 2, by omega⟩, ?_⟩
      change seamPoint2Nat m (2 * m - 2) = w
      rw [seamPoint2Nat_preLast hm rfl, h]
    · refine ⟨⟨m - 1, by omega⟩, ?_⟩
      change seamPoint2Nat m (m - 1) = w
      rw [seamPoint2Nat_hop hm rfl, h]

/-- The active rails of color `c` are exactly the range of the color-`c`
zigzag enumeration. -/
theorem activePred_iff_exists (hm : 4 ≤ m) (c : Fin 3) (w : TerminalQ m) :
    activePred c w ↔ ∃ n : SeamLabel m, seamPoint m c n = w := by
  constructor
  · intro h
    rcases fin3_cases c with rfl | rfl | rfl
    · exact exists_seamPoint0_of_active hm h
    · exact exists_seamPoint1_of_active hm h
    · exact exists_seamPoint2_of_active hm h
  · rintro ⟨n, rfl⟩
    exact seamPoint_active hm c n

/-- Active-set lemma, range form (mirrors `TerminalA2ActiveSet` for H1a):
`ρ_c` moves `w` iff `w` is one of the `2m` zigzag points. -/
theorem rho_ne_self_iff_exists (hm : 4 ≤ m) (c : Fin 3)
    (w : TerminalQ m) :
    rho c w ≠ w ↔ ∃ n : SeamLabel m, seamPoint m c n = w :=
  (rho_ne_self_iff hm c w).trans (activePred_iff_exists hm c w)

end RangeLemmas

/-! ## Bijectivity of the deviation maps (RF2 payload) -/

section Bijectivity

variable {m : Nat} [NeZero m]

theorem rho_injective (hm : 4 ≤ m) (c : Fin 3) :
    Function.Injective (rho (m := m) c) := by
  intro a b hab
  by_cases ha : activePred c a <;> by_cases hb : activePred c b
  · obtain ⟨i, hi⟩ := (activePred_iff_exists hm c a).mp ha
    obtain ⟨j, hj⟩ := (activePred_iff_exists hm c b).mp hb
    rw [← hi, ← hj, rho_seamPoint hm c i, rho_seamPoint hm c j] at hab
    rw [← hi, ← hj]
    exact congrArg _ (seamSucc_injective m (seamPoint_injective hm c hab))
  · exfalso
    obtain ⟨i, hi⟩ := (activePred_iff_exists hm c a).mp ha
    have h1 : rho c b = b := rho_eq_of_not_active hm c hb
    have h2 : activePred c (rho c a) := by
      rw [← hi, rho_seamPoint hm c i]
      exact seamPoint_active hm c (seamSucc m i)
    rw [hab, h1] at h2
    exact hb h2
  · exfalso
    obtain ⟨j, hj⟩ := (activePred_iff_exists hm c b).mp hb
    have h1 : rho c a = a := rho_eq_of_not_active hm c ha
    have h2 : activePred c (rho c b) := by
      rw [← hj, rho_seamPoint hm c j]
      exact seamPoint_active hm c (seamSucc m j)
    rw [← hab, h1] at h2
    exact ha h2
  · rw [← rho_eq_of_not_active hm c ha, ← rho_eq_of_not_active hm c hb]
    exact hab

/-- RF2 payload of the wild layer: each per-color deviation is a
permutation of `(ZMod m)²`. -/
theorem rho_bijective (hm : 4 ≤ m) (c : Fin 3) :
    Function.Bijective (rho (m := m) c) :=
  Finite.injective_iff_bijective.mp (rho_injective hm c)

end Bijectivity

/-! ## The rails as Finsets: cardinality and disjointness -/

/-- The rail `P` as a Finset. -/
def railP (m : Nat) [NeZero m] : Finset (TerminalQ m) :=
  Finset.univ.filter (fun w => memP w)

/-- The rail `Q` as a Finset. -/
def railQ (m : Nat) [NeZero m] : Finset (TerminalQ m) :=
  Finset.univ.filter (fun w => memQ w)

/-- The rail `S` as a Finset. -/
def railS (m : Nat) [NeZero m] : Finset (TerminalQ m) :=
  Finset.univ.filter (fun w => memS w)

/-- The range of the color-`c` zigzag as a Finset. -/
def seamRange (m : Nat) [NeZero m] (c : Fin 3) : Finset (TerminalQ m) :=
  Finset.image (seamPoint m c) Finset.univ

section RailFinsets

variable {m : Nat} [NeZero m]

@[simp] theorem mem_railP {w : TerminalQ m} : w ∈ railP m ↔ memP w := by
  simp [railP]

@[simp] theorem mem_railQ {w : TerminalQ m} : w ∈ railQ m ↔ memQ w := by
  simp [railQ]

@[simp] theorem mem_railS {w : TerminalQ m} : w ∈ railS m ↔ memS w := by
  simp [railS]

@[simp] theorem mem_seamRange {c : Fin 3} {w : TerminalQ m} :
    w ∈ seamRange m c ↔ ∃ n : SeamLabel m, seamPoint m c n = w := by
  simp [seamRange]

theorem card_seamRange (hm : 4 ≤ m) (c : Fin 3) :
    (seamRange m c).card = 2 * m := by
  rw [seamRange,
    Finset.card_image_of_injective _ (seamPoint_injective hm c),
    Finset.card_univ, Fintype.card_fin]

theorem disjoint_railP_railQ (hm : 4 ≤ m) :
    Disjoint (railP m) (railQ m) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  exact memP_memQ_false hm (mem_railP.mp ha) (mem_railQ.mp hb)

theorem disjoint_railP_railS (hm : 4 ≤ m) :
    Disjoint (railP m) (railS m) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  exact memP_memS_false hm (mem_railP.mp ha) (mem_railS.mp hb)

theorem disjoint_railQ_railS (hm : 4 ≤ m) :
    Disjoint (railQ m) (railS m) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  exact memQ_memS_false hm (mem_railQ.mp ha) (mem_railS.mp hb)

/-- The color-0 zigzag covers exactly `P ∪ Q`. -/
theorem seamRange_zero (hm : 4 ≤ m) :
    seamRange m 0 = railP m ∪ railQ m := by
  ext w
  rw [mem_seamRange, Finset.mem_union, mem_railP, mem_railQ]
  constructor
  · rintro ⟨n, rfl⟩
    exact seamPoint_active hm 0 n
  · exact exists_seamPoint0_of_active hm

/-- The color-1 zigzag covers exactly `P ∪ S`. -/
theorem seamRange_one (hm : 4 ≤ m) :
    seamRange m 1 = railP m ∪ railS m := by
  ext w
  rw [mem_seamRange, Finset.mem_union, mem_railP, mem_railS]
  constructor
  · rintro ⟨n, rfl⟩
    exact seamPoint_active hm 1 n
  · exact exists_seamPoint1_of_active hm

/-- The color-2 zigzag covers exactly `Q ∪ S`. -/
theorem seamRange_two (hm : 4 ≤ m) :
    seamRange m 2 = railQ m ∪ railS m := by
  ext w
  rw [mem_seamRange, Finset.mem_union, mem_railQ, mem_railS]
  constructor
  · rintro ⟨n, rfl⟩
    exact seamPoint_active hm 2 n
  · exact exists_seamPoint2_of_active hm

private theorem rail_card_sums (hm : 4 ≤ m) :
    (railP m).card + (railQ m).card = 2 * m ∧
      (railP m).card + (railS m).card = 2 * m ∧
      (railQ m).card + (railS m).card = 2 * m := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Finset.card_union_of_disjoint (disjoint_railP_railQ hm),
      ← seamRange_zero hm, card_seamRange hm]
  · rw [← Finset.card_union_of_disjoint (disjoint_railP_railS hm),
      ← seamRange_one hm, card_seamRange hm]
  · rw [← Finset.card_union_of_disjoint (disjoint_railQ_railS hm),
      ← seamRange_two hm, card_seamRange hm]

/-- The rail `P` has exactly `m` cells. -/
theorem card_railP (hm : 4 ≤ m) : (railP m).card = m := by
  have h := rail_card_sums hm
  omega

/-- The rail `Q` has exactly `m` cells. -/
theorem card_railQ (hm : 4 ≤ m) : (railQ m).card = m := by
  have h := rail_card_sums hm
  omega

/-- The rail `S` has exactly `m` cells. -/
theorem card_railS (hm : 4 ≤ m) : (railS m).card = m := by
  have h := rail_card_sums hm
  omega

end RailFinsets

/-! ## Bridge to the standard root-flat coordinates -/

section RootBridge

open D3TerminalA2Parametric

/-- The wild row read in the standard root section `Fin 2 → ZMod m`. -/
def wildRowRoot {m : Nat} (w : RootState m) : Equiv.Perm (Fin 3) :=
  wildRow (rootPair w)

/-- The color-`c` deviation in the standard root section. -/
def rhoRoot {m : Nat} (c : Fin 3) (w : RootState m) : RootState m :=
  pairRoot (rho c (rootPair w))

theorem rhoRoot_eq_conj {m : Nat} (c : Fin 3) :
    rhoRoot (m := m) c =
      ⇑(rootPairEquiv m).symm ∘ rho c ∘ ⇑(rootPairEquiv m) := rfl

/-- RF2 payload in root coordinates. -/
theorem rhoRoot_bijective {m : Nat} [NeZero m] (hm : 4 ≤ m) (c : Fin 3) :
    Function.Bijective (rhoRoot (m := m) c) := by
  rw [rhoRoot_eq_conj]
  exact ((rootPairEquiv m).symm.bijective.comp
    (rho_bijective hm c)).comp (rootPairEquiv m).bijective

end RootBridge

/-! ## Decide anchors at `m = 4` and `m = 6`

These pin the closed-form `seamPoint` lists against the actual `ρ_c`-orbits
and the rail cardinalities, exactly as printed by
`scripts/search_d3_even_dir.py`. -/

section Anchors

example : ∀ c : Fin 3, ∀ n : SeamLabel 4,
    rho c (seamPoint 4 c n) = seamPoint 4 c (seamSucc 4 n) := by decide

example : ∀ c : Fin 3, ∀ w : TerminalQ 4,
    rho c w ≠ w ↔ ∃ n : SeamLabel 4, seamPoint 4 c n = w := by decide

example :
    (railP 4).card = 4 ∧ (railQ 4).card = 4 ∧ (railS 4).card = 4 := by
  decide

example : ∀ c : Fin 3, ∀ n : SeamLabel 6,
    rho c (seamPoint 6 c n) = seamPoint 6 c (seamSucc 6 n) := by decide

example : ∀ c : Fin 3, ∀ w : TerminalQ 6,
    rho c w ≠ w ↔ ∃ n : SeamLabel 6, seamPoint 6 c n = w := by decide

example :
    (railP 6).card = 6 ∧ (railQ 6).card = 6 ∧ (railS 6).card = 6 := by
  decide

end Anchors

end D3EvenRailSeam
end V28Hard
end EvenV11
