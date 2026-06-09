import EvenV11.V28Hard.D3TerminalA2Parametric
import Shared.Monodromy
import Shared.RankCycle

/-!
# Terminal A2 endpoint rank skeleton

This file records the closed-form inverse rank orders for the active endpoint
cycles in the terminal `A2` carrier proof.  The definitions intentionally use
`Fin (2 * m)` as the primary label type: the rank is then the label itself, and
the map to `TerminalQ m` is the paper endpoint order.

The full H1a proof still needs the parametric rank-step and interval-splice
lemmas.  The finite sanity checks below ensure the formulas agree with the
intended non-colliding endpoint order at the first generic moduli.
-/

namespace EvenV11
namespace V28Hard
namespace TerminalA2EndpointRank

open Shared
open TerminalA2LowMod

attribute [local simp]
  D3TerminalA2Parametric.terminalEndpointEplus
  D3TerminalA2Parametric.terminalEndpointEminus

abbrev EndpointLabel (m : Nat) := Fin (2 * m)

private def negNat {m : Nat} (k : Nat) : ZMod m :=
  -((k : ZMod m))

private def parityEven (k : Nat) : Bool :=
  k % 2 == 0

private theorem zmod_natCast_inj_of_lt {m a b : Nat} [NeZero m]
    (ha : a < m) (hb : b < m) :
    ((a : ZMod m) = (b : ZMod m)) → a = b := by
  intro h
  have hmod := (ZMod.natCast_eq_natCast_iff a b m).mp h
  exact Nat.ModEq.eq_of_lt_of_lt hmod ha hb

private theorem zmod_natCast_ne_of_lt {m a b : Nat} [NeZero m]
    (ha : a < m) (hb : b < m) (hne : a ≠ b) :
    ((a : ZMod m) ≠ (b : ZMod m)) := by
  intro h
  exact hne (zmod_natCast_inj_of_lt ha hb h)

private theorem zmod_small_ne_of_six_le {m a b : Nat} [NeZero m]
    (hm : 6 ≤ m) (ha : a < 6) (hb : b < 6) (hne : a ≠ b) :
    ((a : ZMod m) ≠ (b : ZMod m)) :=
  zmod_natCast_ne_of_lt (by omega) (by omega) hne

private theorem zmod_four_sub_eq_two {m : Nat} [NeZero m] {r : ZMod m} :
    (4 : ZMod m) - r = 2 → r = (2 : ZMod m) := by
  intro h
  have h1 := congrArg (fun x : ZMod m => x + r) h
  have h2 : (4 : ZMod m) = (2 : ZMod m) + r := by
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h1
  have h3 : (2 : ZMod m) + r = (2 : ZMod m) + 2 := by
    calc
      (2 : ZMod m) + r = (4 : ZMod m) := h2.symm
      _ = (2 : ZMod m) + 2 := by norm_num
  exact add_left_cancel h3

private theorem zmod_two_eq_four_sub {m : Nat} [NeZero m] {r : ZMod m} :
    (2 : ZMod m) = (4 : ZMod m) - r → r = (2 : ZMod m) := by
  intro h
  exact zmod_four_sub_eq_two h.symm

private theorem zmod_four_sub_eq_one {m : Nat} [NeZero m] {r : ZMod m} :
    (4 : ZMod m) - r = 1 → r = (3 : ZMod m) := by
  intro h
  have h1 := congrArg (fun x : ZMod m => x + r) h
  have h2 : (4 : ZMod m) = (1 : ZMod m) + r := by
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h1
  have h3 : (1 : ZMod m) + r = (1 : ZMod m) + 3 := by
    calc
      (1 : ZMod m) + r = (4 : ZMod m) := h2.symm
      _ = (1 : ZMod m) + 3 := by norm_num
  exact add_left_cancel h3

private theorem zmod_one_eq_four_sub {m : Nat} [NeZero m] {r : ZMod m} :
    (1 : ZMod m) = (4 : ZMod m) - r → r = (3 : ZMod m) := by
  intro h
  exact zmod_four_sub_eq_one h.symm

private theorem zmod_sub_one_eq_two {m : Nat} [NeZero m] {r : ZMod m} :
    r - 1 = (2 : ZMod m) → r = (3 : ZMod m) := by
  intro h
  have h1 := congrArg (fun x : ZMod m => x + 1) h
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm,
    show (3 : ZMod m) = (2 : ZMod m) + 1 by norm_num] using h1

private theorem zmod_two_eq_sub_one {m : Nat} [NeZero m] {r : ZMod m} :
    (2 : ZMod m) = r - 1 → r = (3 : ZMod m) := by
  intro h
  exact zmod_sub_one_eq_two h.symm

private theorem zmod_sub_two_eq_one {m : Nat} [NeZero m] {r : ZMod m} :
    r - 2 = (1 : ZMod m) → r = (3 : ZMod m) := by
  intro h
  have h1 := congrArg (fun x : ZMod m => x + 2) h
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm,
    show (3 : ZMod m) = (1 : ZMod m) + 2 by norm_num] using h1

private theorem zmod_one_eq_sub_two {m : Nat} [NeZero m] {r : ZMod m} :
    (1 : ZMod m) = r - 2 → r = (3 : ZMod m) := by
  intro h
  exact zmod_sub_two_eq_one h.symm

private theorem natCast_sub_eq_neg_natCast {m a : Nat} [NeZero m]
    (ha : a ≤ m) :
    ((m - a : Nat) : ZMod m) = -(a : ZMod m) := by
  symm
  exact neg_eq_of_add_eq_zero_right (by
    have hsum : a + (m - a) = m := by omega
    calc
      (a : ZMod m) + ((m - a : Nat) : ZMod m)
          = ((a + (m - a : Nat) : Nat) : ZMod m) := by
              norm_num [Nat.cast_add]
      _ = (m : ZMod m) := by rw [hsum]
      _ = 0 := by simp)

private theorem negNat_eq_natCast_of_pos_le {m k a : Nat} [NeZero m]
    (ha0 : 0 < a) (ha : a ≤ m) (hk : k < m) :
    negNat (m := m) k = (a : ZMod m) → k = m - a := by
  intro h
  apply zmod_natCast_inj_of_lt hk (by omega)
  have hneg : (k : ZMod m) = -(a : ZMod m) := by
    simpa [negNat] using congrArg Neg.neg h
  calc
    (k : ZMod m) = -(a : ZMod m) := hneg
    _ = (m - a : Nat) := (natCast_sub_eq_neg_natCast (m := m) (a := a) ha).symm

private theorem negNat_inj_of_lt {m a b : Nat} [NeZero m]
    (ha : a < m) (hb : b < m) :
    negNat (m := m) a = negNat (m := m) b → a = b := by
  intro h
  apply zmod_natCast_inj_of_lt ha hb
  simpa [negNat] using congrArg Neg.neg h

private theorem negNat_eq_zero_of_lt {m k : Nat} [NeZero m]
    (hk : k < m) :
    negNat (m := m) k = 0 → k = 0 := by
  intro h
  apply zmod_natCast_inj_of_lt hk (by
    exact Nat.pos_of_ne_zero (NeZero.ne m))
  simpa [negNat] using congrArg Neg.neg h

private theorem two_sub_natCast_eq_three_forces {m d : Nat} [NeZero m]
    (hm : 6 ≤ m) (hd : d < m) :
    ((2 : ZMod m) - (d : ZMod m) = (3 : ZMod m)) → d = m - 1 := by
  intro h
  apply zmod_natCast_inj_of_lt hd (by omega)
  have hdneg : (d : ZMod m) = -(1 : ZMod m) := by
    have h1 := congrArg (fun x : ZMod m => x + (d : ZMod m)) h
    have h2 : (2 : ZMod m) = (3 : ZMod m) + (d : ZMod m) := by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h1
    have h3 : (d : ZMod m) + (1 : ZMod m) = 0 := by
      calc
        (d : ZMod m) + (1 : ZMod m)
            = ((3 : ZMod m) + (d : ZMod m)) - (2 : ZMod m) := by ring
        _ = (2 : ZMod m) - (2 : ZMod m) := by rw [← h2]
        _ = 0 := by simp
    exact eq_neg_of_add_eq_zero_left h3
  calc
    (d : ZMod m) = -(1 : ZMod m) := hdneg
    _ = ((m - 1 : Nat) : ZMod m) := by
      simpa using (natCast_sub_eq_neg_natCast (m := m) (a := 1) (by omega)).symm

private theorem four_add_natCast_eq_three_forces {m d : Nat} [NeZero m]
    (hm : 6 ≤ m) (hd : d < m) :
    ((4 : ZMod m) + (d : ZMod m) = (3 : ZMod m)) → d = m - 1 := by
  intro h
  apply zmod_natCast_inj_of_lt hd (by omega)
  have hdneg : (d : ZMod m) = -(1 : ZMod m) := by
    have h3 : (d : ZMod m) + (1 : ZMod m) = 0 := by
      calc
        (d : ZMod m) + (1 : ZMod m)
            = ((4 : ZMod m) + (d : ZMod m)) - (3 : ZMod m) := by ring
        _ = (3 : ZMod m) - (3 : ZMod m) := by rw [h]
        _ = 0 := by simp
    exact eq_neg_of_add_eq_zero_left h3
  calc
    (d : ZMod m) = -(1 : ZMod m) := hdneg
    _ = ((m - 1 : Nat) : ZMod m) := by
      simpa using (natCast_sub_eq_neg_natCast (m := m) (a := 1) (by omega)).symm

private theorem negNat_ne_two_of_lt_m_sub_two {m k : Nat} [NeZero m]
    (hm : 6 ≤ m) (hk : k < m - 2) :
    negNat (m := m) k ≠ (2 : ZMod m) := by
  intro h
  have hk' : k = m - 2 :=
    negNat_eq_natCast_of_pos_le (m := m) (k := k) (a := 2)
      (by omega) (by omega) (by omega) h
  omega

private theorem two_sub_natCast_ne_three_of_lt_m_sub_one {m d : Nat}
    [NeZero m] (hm : 6 ≤ m) (hd : d < m - 1) :
    (2 : ZMod m) - (d : ZMod m) ≠ (3 : ZMod m) := by
  intro h
  have hd' := two_sub_natCast_eq_three_forces (m := m) (d := d) hm (by omega) h
  omega

private theorem four_add_natCast_ne_three_of_lt_m_sub_one {m d : Nat}
    [NeZero m] (hm : 6 ≤ m) (hd : d < m - 1) :
    (4 : ZMod m) + (d : ZMod m) ≠ (3 : ZMod m) := by
  intro h
  have hd' := four_add_natCast_eq_three_forces (m := m) (d := d) hm (by omega) h
  omega

private theorem endpoint0_generic_AB_collision {m : Nat} [NeZero m]
    {r s : ZMod m} :
    ((r, (2 : ZMod m)) : TerminalQ m) = (s, (4 : ZMod m) - s) →
    r = (2 : ZMod m) ∧ s = (2 : ZMod m) := by
  intro h
  have hx : r = s := congrArg Prod.fst h
  have hy : (2 : ZMod m) = (4 : ZMod m) - s := congrArg Prod.snd h
  have hs : s = (2 : ZMod m) := by
    have h1 := congrArg (fun x : ZMod m => x + s) hy
    have h2 : (2 : ZMod m) + s = (4 : ZMod m) := by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h1
    have h3 : s + (2 : ZMod m) = (2 : ZMod m) + (2 : ZMod m) := by
      simpa [add_comm,
        show (4 : ZMod m) = (2 : ZMod m) + (2 : ZMod m) by norm_num] using h2
    exact add_right_cancel h3
  exact ⟨hx.trans hs, hs⟩

private theorem endpoint1_generic_AB_collision {m : Nat} [NeZero m]
    {r s : ZMod m} :
    (((1 : ZMod m), r) : TerminalQ m) = ((4 : ZMod m) - s, s) →
    r = (3 : ZMod m) ∧ s = (3 : ZMod m) := by
  intro h
  have hx : (1 : ZMod m) = (4 : ZMod m) - s := congrArg Prod.fst h
  have hy : r = s := congrArg Prod.snd h
  have hs : s = (3 : ZMod m) := by
    have h1 := congrArg (fun x : ZMod m => x + s) hx
    have h2 : (1 : ZMod m) + s = (4 : ZMod m) := by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h1
    have h3 : s + (1 : ZMod m) = (3 : ZMod m) + (1 : ZMod m) := by
      simpa [add_comm,
        show (4 : ZMod m) = (3 : ZMod m) + (1 : ZMod m) by norm_num] using h2
    exact add_right_cancel h3
  exact ⟨hy.trans hs, hs⟩

private theorem endpoint2_generic_AB_collision {m : Nat} [NeZero m]
    {r s : ZMod m} :
    (((1 : ZMod m), r - 1) : TerminalQ m) = (s - 2, (2 : ZMod m)) →
    r = (3 : ZMod m) ∧ s = (3 : ZMod m) := by
  intro h
  have hx : (1 : ZMod m) = s - 2 := congrArg Prod.fst h
  have hy : r - 1 = (2 : ZMod m) := congrArg Prod.snd h
  have hr : r = (3 : ZMod m) := by
    have h1 := congrArg (fun x : ZMod m => x + 1) hy
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm,
      show (3 : ZMod m) = (2 : ZMod m) + (1 : ZMod m) by norm_num] using h1
  have hs : s = (3 : ZMod m) := by
    have h1 := congrArg (fun x : ZMod m => x + 2) hx
    have h2 : s = (1 : ZMod m) + 2 := by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h1.symm
    simpa [show (3 : ZMod m) = (1 : ZMod m) + (2 : ZMod m) by norm_num] using h2
  exact ⟨hr, hs⟩

/-- In the paper endpoint coordinates, a generic `A`/`B` collision can occur
only on one of the exceptional fibers. -/
theorem terminalEndpointA_eq_B_forces_exception {m : Nat} [NeZero m]
    (c : TorusColor 3) (r s : ZMod m) :
    D3TerminalA2Parametric.terminalEndpointA (m := m) c r =
      D3TerminalA2Parametric.terminalEndpointB (m := m) c s →
    D3TerminalA2Parametric.terminalEndpointException (m := m) c r ∧
      D3TerminalA2Parametric.terminalEndpointException (m := m) c s := by
  fin_cases c
  · intro h
    have hs := endpoint0_generic_AB_collision h
    simp [D3TerminalA2Parametric.terminalEndpointException, hs.1, hs.2]
  · intro h
    have hs := endpoint1_generic_AB_collision h
    simp [D3TerminalA2Parametric.terminalEndpointException, hs.1, hs.2]
  · intro h
    have hs := endpoint2_generic_AB_collision h
    simp [D3TerminalA2Parametric.terminalEndpointException, hs.1, hs.2]

/-- A non-exceptional `A` endpoint cannot collide with any `B` endpoint. -/
theorem terminalEndpointA_ne_B_of_not_exception_left {m : Nat} [NeZero m]
    (c : TorusColor 3) (r s : ZMod m)
    (hr : ¬ D3TerminalA2Parametric.terminalEndpointException (m := m) c r) :
    D3TerminalA2Parametric.terminalEndpointA (m := m) c r ≠
      D3TerminalA2Parametric.terminalEndpointB (m := m) c s := by
  intro h
  exact hr ((terminalEndpointA_eq_B_forces_exception c r s h).1)

/-- A non-exceptional `B` endpoint cannot collide with any `A` endpoint. -/
theorem terminalEndpointA_ne_B_of_not_exception_right {m : Nat} [NeZero m]
    (c : TorusColor 3) (r s : ZMod m)
    (hs : ¬ D3TerminalA2Parametric.terminalEndpointException (m := m) c s) :
    D3TerminalA2Parametric.terminalEndpointA (m := m) c r ≠
      D3TerminalA2Parametric.terminalEndpointB (m := m) c s := by
  intro h
  exact hs ((terminalEndpointA_eq_B_forces_exception c r s h).2)

/-- The generic `A_i(r)` endpoints have no repeated fiber index. -/
theorem terminalEndpointA_injective {m : Nat} [NeZero m]
    (c : TorusColor 3) :
    Function.Injective (D3TerminalA2Parametric.terminalEndpointA (m := m) c) := by
  fin_cases c
  · intro r s h
    exact congrArg Prod.fst h
  · intro r s h
    exact congrArg Prod.snd h
  · intro r s h
    have hy : r - 1 = s - 1 := congrArg Prod.snd h
    have hplus := congrArg (fun x : ZMod m => x + 1) hy
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hplus

/-- The generic `B_i(r)` endpoints have no repeated fiber index. -/
theorem terminalEndpointB_injective {m : Nat} [NeZero m]
    (c : TorusColor 3) :
    Function.Injective (D3TerminalA2Parametric.terminalEndpointB (m := m) c) := by
  fin_cases c
  · intro r s h
    exact congrArg Prod.fst h
  · intro r s h
    exact congrArg Prod.snd h
  · intro r s h
    have hx : r - 2 = s - 2 := congrArg Prod.fst h
    have hplus := congrArg (fun x : ZMod m => x + 2) hx
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hplus

private instance instTwoMulNeZero (m : Nat) [NeZero m] : NeZero (2 * m) :=
  ⟨Nat.mul_ne_zero (by decide) (NeZero.ne m)⟩

/-- Endpoint labels as used in the manuscript rank order: generic `A` and `B`
endpoints, plus the two puncture endpoints replacing the collision fiber. -/
inductive EndpointDesc (m : Nat) where
  | A (r : ZMod m)
  | B (r : ZMod m)
  | Eplus
  | Eminus
  deriving DecidableEq

/-- Interpret an endpoint descriptor as an actual terminal point for a fixed
color. -/
def endpointDescPoint {m : Nat} :
    TorusColor 3 → EndpointDesc m → TerminalQ m
  | c, EndpointDesc.A r =>
      D3TerminalA2Parametric.terminalEndpointA (m := m) c r
  | c, EndpointDesc.B r =>
      D3TerminalA2Parametric.terminalEndpointB (m := m) c r
  | c, EndpointDesc.Eplus =>
      D3TerminalA2Parametric.terminalEndpointEplus (m := m) c
  | c, EndpointDesc.Eminus =>
      D3TerminalA2Parametric.terminalEndpointEminus (m := m) c

def endpointCollisionIndex {m : Nat} : TorusColor 3 → ZMod m
  | 0 => 2
  | 1 => 3
  | _ => 3

def endpointDescValid {m : Nat} (c : TorusColor 3) : EndpointDesc m → Prop
  | EndpointDesc.A r => r ≠ endpointCollisionIndex (m := m) c
  | EndpointDesc.B r => r ≠ endpointCollisionIndex (m := m) c
  | EndpointDesc.Eplus => True
  | EndpointDesc.Eminus => True

/-- Paper endpoint successor on descriptors, including the puncture bridge
vertices.  Invalid collision descriptors are assigned to the generic branch;
the theorem below only uses this function on `endpointDescValid` descriptors. -/
def endpointDescSucc {m : Nat} :
    TorusColor 3 → EndpointDesc m → EndpointDesc m
  | 0, EndpointDesc.A r =>
      if r = (3 : ZMod m) then EndpointDesc.Eminus else EndpointDesc.B (r - 1)
  | 0, EndpointDesc.B r =>
      if r = (3 : ZMod m) then EndpointDesc.Eplus else EndpointDesc.A (r - 1)
  | 0, EndpointDesc.Eplus => EndpointDesc.A (1 : ZMod m)
  | 0, EndpointDesc.Eminus => EndpointDesc.B (1 : ZMod m)
  | 1, EndpointDesc.A r =>
      if r = (4 : ZMod m) then EndpointDesc.Eplus else EndpointDesc.B (r - 1)
  | 1, EndpointDesc.B r =>
      if r = (4 : ZMod m) then EndpointDesc.Eminus else EndpointDesc.A (r - 1)
  | 1, EndpointDesc.Eplus => EndpointDesc.B (2 : ZMod m)
  | 1, EndpointDesc.Eminus => EndpointDesc.A (2 : ZMod m)
  | _, EndpointDesc.A r =>
      if r = (2 : ZMod m) then EndpointDesc.Eminus else EndpointDesc.B (r + 1)
  | _, EndpointDesc.B r =>
      if r = (2 : ZMod m) then EndpointDesc.Eplus else EndpointDesc.A (r + 1)
  | _, EndpointDesc.Eplus => EndpointDesc.A (4 : ZMod m)
  | _, EndpointDesc.Eminus => EndpointDesc.B (4 : ZMod m)

/-- The paper recurrence record advances every valid descriptor by
`endpointDescSucc`.  This is the recurrence-to-rank handoff before unfolding the
closed-form rank list. -/
theorem terminalCompressedEndpointReturn_endpointDescSucc {m : Nat} [NeZero m]
    (rec : D3TerminalA2Parametric.TerminalA2EndpointRecurrence m)
    (c : TorusColor 3) (d : EndpointDesc m)
    (hvalid : endpointDescValid (m := m) c d) :
    D3TerminalA2Parametric.terminalCompressedEndpointReturn
        (m := m) rec.exchange c (endpointDescPoint (m := m) c d) =
      endpointDescPoint (m := m) c (endpointDescSucc c d) := by
  fin_cases c <;> cases d
  · rename_i r
    simp [endpointDescValid, endpointCollisionIndex] at hvalid
    by_cases h3 : r = (3 : ZMod m)
    · subst r
      simpa [endpointDescSucc, endpointDescPoint] using rec.boundary0_A3
    · have hex :
          ¬ D3TerminalA2Parametric.terminalEndpointException (m := m)
            (0 : TorusColor 3) r := by
        simp [D3TerminalA2Parametric.terminalEndpointException, hvalid, h3]
      simpa [endpointDescSucc, endpointDescPoint, h3,
        D3TerminalA2Parametric.terminalEndpointNext] using
          rec.generic_A (0 : TorusColor 3) r hex
  · rename_i r
    simp [endpointDescValid, endpointCollisionIndex] at hvalid
    by_cases h3 : r = (3 : ZMod m)
    · subst r
      simpa [endpointDescSucc, endpointDescPoint] using rec.boundary0_B3
    · have hex :
          ¬ D3TerminalA2Parametric.terminalEndpointException (m := m)
            (0 : TorusColor 3) r := by
        simp [D3TerminalA2Parametric.terminalEndpointException, hvalid, h3]
      simpa [endpointDescSucc, endpointDescPoint, h3,
        D3TerminalA2Parametric.terminalEndpointNext] using
          rec.generic_B (0 : TorusColor 3) r hex
  · simpa [endpointDescSucc, endpointDescPoint] using rec.boundary0_Eplus
  · simpa [endpointDescSucc, endpointDescPoint] using rec.boundary0_Eminus
  · rename_i r
    simp [endpointDescValid, endpointCollisionIndex] at hvalid
    by_cases h4 : r = (4 : ZMod m)
    · subst r
      simpa [endpointDescSucc, endpointDescPoint] using rec.boundary1_A4
    · have hex :
          ¬ D3TerminalA2Parametric.terminalEndpointException (m := m)
            (1 : TorusColor 3) r := by
        simp [D3TerminalA2Parametric.terminalEndpointException, hvalid, h4]
      simpa [endpointDescSucc, endpointDescPoint, h4,
        D3TerminalA2Parametric.terminalEndpointNext] using
          rec.generic_A (1 : TorusColor 3) r hex
  · rename_i r
    simp [endpointDescValid, endpointCollisionIndex] at hvalid
    by_cases h4 : r = (4 : ZMod m)
    · subst r
      simpa [endpointDescSucc, endpointDescPoint] using rec.boundary1_B4
    · have hex :
          ¬ D3TerminalA2Parametric.terminalEndpointException (m := m)
            (1 : TorusColor 3) r := by
        simp [D3TerminalA2Parametric.terminalEndpointException, hvalid, h4]
      simpa [endpointDescSucc, endpointDescPoint, h4,
        D3TerminalA2Parametric.terminalEndpointNext] using
          rec.generic_B (1 : TorusColor 3) r hex
  · simpa [endpointDescSucc, endpointDescPoint] using rec.boundary1_Eplus
  · simpa [endpointDescSucc, endpointDescPoint] using rec.boundary1_Eminus
  · rename_i r
    simp [endpointDescValid, endpointCollisionIndex] at hvalid
    by_cases h2 : r = (2 : ZMod m)
    · subst r
      simpa [endpointDescSucc, endpointDescPoint] using rec.boundary2_A2
    · have hex :
          ¬ D3TerminalA2Parametric.terminalEndpointException (m := m)
            (2 : TorusColor 3) r := by
        simp [D3TerminalA2Parametric.terminalEndpointException, hvalid, h2]
      simpa [endpointDescSucc, endpointDescPoint, h2,
        D3TerminalA2Parametric.terminalEndpointNext] using
          rec.generic_A (2 : TorusColor 3) r hex
  · rename_i r
    simp [endpointDescValid, endpointCollisionIndex] at hvalid
    by_cases h2 : r = (2 : ZMod m)
    · subst r
      simpa [endpointDescSucc, endpointDescPoint] using rec.boundary2_B2
    · have hex :
          ¬ D3TerminalA2Parametric.terminalEndpointException (m := m)
            (2 : TorusColor 3) r := by
        simp [D3TerminalA2Parametric.terminalEndpointException, hvalid, h2]
      simpa [endpointDescSucc, endpointDescPoint, h2,
        D3TerminalA2Parametric.terminalEndpointNext] using
          rec.generic_B (2 : TorusColor 3) r hex
  · simpa [endpointDescSucc, endpointDescPoint] using rec.boundary2_Eplus
  · simpa [endpointDescSucc, endpointDescPoint] using rec.boundary2_Eminus

/-- The rank-successor map on endpoint labels.  The future `h_i` rank-step
lemma should identify the paper endpoint successor with this map. -/
def endpointRankSucc (m : Nat) [NeZero m] :
    EndpointLabel m → EndpointLabel m :=
  fun n =>
    ⟨(n.val + 1) % (2 * m), by
      have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
      exact Nat.mod_lt _ (Nat.mul_pos (by decide) hm)⟩

/-- Rank equivalence for endpoint labels, definitionally `n.val`. -/
def endpointRankEquiv (m : Nat) [NeZero m] :
    EndpointLabel m ≃ ZMod (2 * m) where
  toFun n := (n.val : ZMod (2 * m))
  invFun z := ⟨z.val, z.val_lt⟩
  left_inv n := by
    apply Fin.ext
    simp [ZMod.val_natCast_of_lt n.isLt]
  right_inv z := by
    exact ZMod.natCast_zmod_val z

theorem endpointRankSucc_rank_step {m : Nat} [NeZero m]
    (n : EndpointLabel m) :
    endpointRankEquiv m (endpointRankSucc m n) =
      endpointRankEquiv m n + 1 := by
  change (((n.val + 1) % (2 * m) : Nat) : ZMod (2 * m)) =
    (n.val : ZMod (2 * m)) + 1
  rw [ZMod.natCast_mod]
  simp [Nat.cast_add]

/-- The abstract endpoint rank successor is a single cycle of length `2m`. -/
theorem endpointRankSucc_singleCycle {m : Nat} [NeZero m] :
    Shared.IsSingleCycleMap (endpointRankSucc m) :=
  Shared.single_cycle_of_zmod_rank_equiv
    (endpointRankSucc m) (endpointRankEquiv m) endpointRankSucc_rank_step

/-- Color-0 inverse endpoint rank order. -/
def endpoint0Desc (m : Nat) [NeZero m] (n : EndpointLabel m) :
    EndpointDesc m :=
  let k := n.val
  if k = m - 2 then
    EndpointDesc.Eplus
  else if k = m - 1 then
    EndpointDesc.A (1 : ZMod m)
  else if k = 2 * m - 2 then
    EndpointDesc.Eminus
  else if k = 2 * m - 1 then
    EndpointDesc.B (1 : ZMod m)
  else if k < m - 2 then
    let r : ZMod m := negNat k
    if parityEven k then
      EndpointDesc.A r
    else
      EndpointDesc.B r
  else if k < 2 * m - 2 then
    let d := k - m
    let r : ZMod m := negNat d
    if parityEven d then
      EndpointDesc.B r
    else
      EndpointDesc.A r
  else
    EndpointDesc.A (0 : ZMod m)

/-- Color-0 inverse endpoint rank order. -/
def endpoint0Point (m : Nat) [NeZero m] (n : EndpointLabel m) :
    TerminalQ m :=
  let k := n.val
  if k = m - 2 then
    ((2 : ZMod m), (3 : ZMod m))
  else if k = m - 1 then
    ((1 : ZMod m), (2 : ZMod m))
  else if k = 2 * m - 2 then
    ((2 : ZMod m), (1 : ZMod m))
  else if k = 2 * m - 1 then
    ((1 : ZMod m), (3 : ZMod m))
  else if k < m - 2 then
    let r : ZMod m := negNat k
    if parityEven k then
      (r, (2 : ZMod m))
    else
      (r, (4 : ZMod m) - r)
  else if k < 2 * m - 2 then
    let d := k - m
    let r : ZMod m := negNat d
    if parityEven d then
      (r, (4 : ZMod m) - r)
    else
      (r, (2 : ZMod m))
  else
    ((0 : ZMod m), (0 : ZMod m))

/-- Color-1 inverse endpoint rank order. -/
def endpoint1Desc (m : Nat) [NeZero m] (n : EndpointLabel m) :
    EndpointDesc m :=
  let k := n.val
  if k = 0 then
    EndpointDesc.Eplus
  else if k = m then
    EndpointDesc.Eminus
  else if k < m then
    let d := k - 1
    let r : ZMod m := (2 : ZMod m) - (d : ZMod m)
    if parityEven d then
      EndpointDesc.B r
    else
      EndpointDesc.A r
  else
    let d := k - (m + 1)
    let r : ZMod m := (2 : ZMod m) - (d : ZMod m)
    if parityEven d then
      EndpointDesc.A r
    else
      EndpointDesc.B r

/-- Color-1 inverse endpoint rank order. -/
def endpoint1Point (m : Nat) [NeZero m] (n : EndpointLabel m) :
    TerminalQ m :=
  let k := n.val
  if k = 0 then
    ((0 : ZMod m), (3 : ZMod m))
  else if k = m then
    ((2 : ZMod m), (3 : ZMod m))
  else if k < m then
    let d := k - 1
    let r : ZMod m := (2 : ZMod m) - (d : ZMod m)
    if parityEven d then
      ((4 : ZMod m) - r, r)
    else
      ((1 : ZMod m), r)
  else
    let d := k - (m + 1)
    let r : ZMod m := (2 : ZMod m) - (d : ZMod m)
    if parityEven d then
      ((1 : ZMod m), r)
    else
      ((4 : ZMod m) - r, r)

/-- Color-2 inverse endpoint rank order. -/
def endpoint2Desc (m : Nat) [NeZero m] (n : EndpointLabel m) :
    EndpointDesc m :=
  let k := n.val
  if k = 0 then
    EndpointDesc.B (2 : ZMod m)
  else if k = 1 then
    EndpointDesc.Eplus
  else if k = m + 1 then
    EndpointDesc.Eminus
  else if k ≤ m then
    let d := k - 2
    let r : ZMod m := (4 : ZMod m) + (d : ZMod m)
    if parityEven d then
      EndpointDesc.A r
    else
      EndpointDesc.B r
  else
    let d := k - (m + 2)
    let r : ZMod m := (4 : ZMod m) + (d : ZMod m)
    if parityEven d then
      EndpointDesc.B r
    else
      EndpointDesc.A r

/-- Color-2 inverse endpoint rank order. -/
def endpoint2Point (m : Nat) [NeZero m] (n : EndpointLabel m) :
    TerminalQ m :=
  let k := n.val
  if k = 0 then
    ((0 : ZMod m), (2 : ZMod m))
  else if k = 1 then
    ((2 : ZMod m), (1 : ZMod m))
  else if k = m + 1 then
    ((0 : ZMod m), (3 : ZMod m))
  else if k ≤ m then
    let d := k - 2
    let r : ZMod m := (4 : ZMod m) + (d : ZMod m)
    if parityEven d then
      ((1 : ZMod m), r - 1)
    else
      (r - 2, (2 : ZMod m))
  else
    let d := k - (m + 2)
    let r : ZMod m := (4 : ZMod m) + (d : ZMod m)
    if parityEven d then
      (r - 2, (2 : ZMod m))
    else
      ((1 : ZMod m), r - 1)

def endpointPoint (m : Nat) [NeZero m] :
    TorusColor 3 → EndpointLabel m → TerminalQ m
  | 0 => endpoint0Point m
  | 1 => endpoint1Point m
  | _ => endpoint2Point m

def endpointDesc (m : Nat) [NeZero m] :
    TorusColor 3 → EndpointLabel m → EndpointDesc m
  | 0 => endpoint0Desc m
  | 1 => endpoint1Desc m
  | _ => endpoint2Desc m

private def endpointLabelOfNat? (m : Nat) [NeZero m] (k : Nat) :
    Option (EndpointLabel m) :=
  if h : k < 2 * m then
    some ⟨k, h⟩
  else
    none

@[simp] private theorem endpointLabelOfNat?_val {m : Nat} [NeZero m]
    (n : EndpointLabel m) :
    endpointLabelOfNat? m n.val = some n := by
  simp [endpointLabelOfNat?, n.isLt]

private theorem endpointLabelOfNat?_eq_some_of_val {m k : Nat} [NeZero m]
    {n : EndpointLabel m} (hn : n.val = k) :
    endpointLabelOfNat? m k = some n := by
  rw [← hn]
  exact endpointLabelOfNat?_val n

private theorem val_neg_negNat_of_lt {m k : Nat} [NeZero m]
    (hk : k < m) :
    (-(negNat (m := m) k)).val = k := by
  have h : (-(negNat (m := m) k)) = (k : ZMod m) := by
    simp [negNat]
  rw [h]
  exact ZMod.val_natCast_of_lt hk

private theorem negNat_ne_one_of_lt_m_sub_one {m k : Nat} [NeZero m]
    (hm : 6 ≤ m) (hk : k < m - 1) :
    negNat (m := m) k ≠ (1 : ZMod m) := by
  intro h
  have h' : negNat (m := m) k = ((1 : Nat) : ZMod m) := by
    simpa using h
  have hk' : k = m - 1 :=
    negNat_eq_natCast_of_pos_le (m := m) (k := k) (a := 1)
      (by omega) (by omega) (by omega) h'
  omega

private def endpoint0DescRank? (m : Nat) [NeZero m] :
    EndpointDesc m → Option (EndpointLabel m)
  | EndpointDesc.Eplus => endpointLabelOfNat? m (m - 2)
  | EndpointDesc.Eminus => endpointLabelOfNat? m (2 * m - 2)
  | EndpointDesc.A r =>
      if r = (1 : ZMod m) then
        endpointLabelOfNat? m (m - 1)
      else
        let d := (-r).val
        if parityEven d then
          endpointLabelOfNat? m d
        else
          endpointLabelOfNat? m (m + d)
  | EndpointDesc.B r =>
      if r = (1 : ZMod m) then
        endpointLabelOfNat? m (2 * m - 1)
      else
        let d := (-r).val
        if parityEven d then
          endpointLabelOfNat? m (m + d)
        else
          endpointLabelOfNat? m d

private theorem zmod_two_sub_two_sub_val {m d : Nat} [NeZero m]
    (hd : d < m) :
    ((2 : ZMod m) - ((2 : ZMod m) - (d : ZMod m))).val = d := by
  have h : (2 : ZMod m) - ((2 : ZMod m) - (d : ZMod m)) = (d : ZMod m) := by
    ring
  rw [h]
  exact ZMod.val_natCast_of_lt hd

private theorem zmod_four_add_sub_four_val {m d : Nat} [NeZero m]
    (hd : d < m) :
    (((4 : ZMod m) + (d : ZMod m)) - (4 : ZMod m)).val = d := by
  have h : ((4 : ZMod m) + (d : ZMod m)) - (4 : ZMod m) = (d : ZMod m) := by
    ring
  rw [h]
  exact ZMod.val_natCast_of_lt hd

private theorem four_add_natCast_eq_two_forces {m d : Nat} [NeZero m]
    (hm : 6 ≤ m) (hd : d < m) :
    ((4 : ZMod m) + (d : ZMod m) = (2 : ZMod m)) → d = m - 2 := by
  intro h
  apply zmod_natCast_inj_of_lt hd (by omega)
  have hdneg : (d : ZMod m) = -(2 : ZMod m) := by
    have h0 : (d : ZMod m) + (2 : ZMod m) = 0 := by
      calc
        (d : ZMod m) + (2 : ZMod m)
            = ((4 : ZMod m) + (d : ZMod m)) - (2 : ZMod m) := by ring
        _ = (2 : ZMod m) - (2 : ZMod m) := by rw [h]
        _ = 0 := by simp
    exact eq_neg_of_add_eq_zero_left h0
  calc
    (d : ZMod m) = -(2 : ZMod m) := hdneg
    _ = ((m - 2 : Nat) : ZMod m) := by
      simpa using (natCast_sub_eq_neg_natCast (m := m) (a := 2) (by omega)).symm

private theorem parityEven_sub_two_of_even {m : Nat}
    (hmEven : Even m) (hm : 2 ≤ m) :
    parityEven (m - 2) = true := by
  rcases hmEven with ⟨t, rfl⟩
  have ht : 1 ≤ t := by omega
  have hsub : t + t - 2 = 2 * (t - 1) := by omega
  simp [parityEven, hsub]

private theorem parityEven_sub_two_of_odd {m : Nat}
    (hmOdd : Odd m) (hm : 2 ≤ m) :
    parityEven (m - 2) = false := by
  rcases hmOdd with ⟨t, rfl⟩
  have ht : 1 ≤ t := by omega
  have hsub : 2 * t + 1 - 2 = 2 * (t - 1) + 1 := by omega
  rw [hsub]
  simp [parityEven]

private def endpoint1DescRank? (m : Nat) [NeZero m] :
    EndpointDesc m → Option (EndpointLabel m)
  | EndpointDesc.Eplus => endpointLabelOfNat? m 0
  | EndpointDesc.Eminus => endpointLabelOfNat? m m
  | EndpointDesc.A r =>
      let d := ((2 : ZMod m) - r).val
      if parityEven d then
        endpointLabelOfNat? m (m + 1 + d)
      else
        endpointLabelOfNat? m (1 + d)
  | EndpointDesc.B r =>
      let d := ((2 : ZMod m) - r).val
      if parityEven d then
        endpointLabelOfNat? m (1 + d)
      else
        endpointLabelOfNat? m (m + 1 + d)

private def endpoint2DescRank? (m : Nat) [NeZero m] :
    EndpointDesc m → Option (EndpointLabel m)
  | EndpointDesc.Eplus => endpointLabelOfNat? m 1
  | EndpointDesc.Eminus => endpointLabelOfNat? m (m + 1)
  | EndpointDesc.A r =>
      let d := (r - (4 : ZMod m)).val
      if parityEven d then
        endpointLabelOfNat? m (2 + d)
      else
        endpointLabelOfNat? m (m + 2 + d)
  | EndpointDesc.B r =>
      if r = (2 : ZMod m) then
        endpointLabelOfNat? m 0
      else
        let d := (r - (4 : ZMod m)).val
        if parityEven d then
          endpointLabelOfNat? m (m + 2 + d)
        else
          endpointLabelOfNat? m (2 + d)

set_option maxHeartbeats 2000000 in
theorem endpoint0DescRank?_endpoint0Desc {m : Nat} [NeZero m]
    (hm : 6 ≤ m) (n : EndpointLabel m) :
    endpoint0DescRank? m (endpoint0Desc m n) = some n := by
  simp only [endpoint0Desc]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · simp [endpoint0DescRank?]
    exact endpointLabelOfNat?_eq_some_of_val h1
  · simp [endpoint0DescRank?]
    exact endpointLabelOfNat?_eq_some_of_val h2
  · simp [endpoint0DescRank?]
    exact endpointLabelOfNat?_eq_some_of_val h3
  · simp [endpoint0DescRank?]
    exact endpointLabelOfNat?_eq_some_of_val h4
  · have hk : n.val < m := by omega
    have hd : (-(negNat (m := m) n.val)).val = n.val :=
      val_neg_negNat_of_lt hk
    have hr1 : negNat (m := m) n.val ≠ (1 : ZMod m) :=
      negNat_ne_one_of_lt_m_sub_one hm (by omega)
    simp_all [endpoint0DescRank?]
  · have hk : n.val < m := by omega
    have hd : (-(negNat (m := m) n.val)).val = n.val :=
      val_neg_negNat_of_lt hk
    have hr1 : negNat (m := m) n.val ≠ (1 : ZMod m) :=
      negNat_ne_one_of_lt_m_sub_one hm (by omega)
    simp_all [endpoint0DescRank?]
  · let d := n.val - m
    have hdlt : d < m := by
      have hnlt : n.val < 2 * m := n.isLt
      omega
    have hdval : (-(negNat (m := m) d)).val = d :=
      val_neg_negNat_of_lt hdlt
    have hr1 : negNat (m := m) d ≠ (1 : ZMod m) :=
      negNat_ne_one_of_lt_m_sub_one hm (by omega)
    have hdval' :
        (-(negNat (m := m) (n.val - m))).val = n.val - m := by
      simpa [d] using hdval
    have hr1' : negNat (m := m) (n.val - m) ≠ (1 : ZMod m) := by
      simpa [d] using hr1
    simp_all [endpoint0DescRank?]
    exact endpointLabelOfNat?_eq_some_of_val (by omega)
  · let d := n.val - m
    have hdlt : d < m := by
      have hnlt : n.val < 2 * m := n.isLt
      omega
    have hdval : (-(negNat (m := m) d)).val = d :=
      val_neg_negNat_of_lt hdlt
    have hr1 : negNat (m := m) d ≠ (1 : ZMod m) :=
      negNat_ne_one_of_lt_m_sub_one hm (by omega)
    have hdval' :
        (-(negNat (m := m) (n.val - m))).val = n.val - m := by
      simpa [d] using hdval
    have hr1' : negNat (m := m) (n.val - m) ≠ (1 : ZMod m) := by
      simpa [d] using hr1
    simp_all [endpoint0DescRank?]
    exact endpointLabelOfNat?_eq_some_of_val (by omega)
  · exfalso
    have hnlt : n.val < 2 * m := n.isLt
    omega

set_option maxHeartbeats 2000000 in
theorem endpoint1DescRank?_endpoint1Desc {m : Nat} [NeZero m]
    (hm : 6 ≤ m) (n : EndpointLabel m) :
    endpoint1DescRank? m (endpoint1Desc m n) = some n := by
  simp only [endpoint1Desc]
  split_ifs with h1 h2 h3 h4 h5
  · simp [endpoint1DescRank?]
    exact endpointLabelOfNat?_eq_some_of_val h1
  · simp [endpoint1DescRank?]
    exact endpointLabelOfNat?_eq_some_of_val h2
  · let d := n.val - 1
    have hnpos : 0 < n.val := by
      omega
    have hdlt : d < m := by omega
    have hdval :
        ((2 : ZMod m) - ((2 : ZMod m) - (d : ZMod m))).val = d :=
      zmod_two_sub_two_sub_val hdlt
    have hdval' :
        ((2 : ZMod m) - ((2 : ZMod m) - ((n.val - 1 : Nat) : ZMod m))).val =
          n.val - 1 := by
      simpa [d] using hdval
    simp_all [endpoint1DescRank?]
    exact endpointLabelOfNat?_eq_some_of_val (by omega)
  · let d := n.val - 1
    have hnpos : 0 < n.val := by
      omega
    have hdlt : d < m := by omega
    have hdval :
        ((2 : ZMod m) - ((2 : ZMod m) - (d : ZMod m))).val = d :=
      zmod_two_sub_two_sub_val hdlt
    have hdval' :
        ((2 : ZMod m) - ((2 : ZMod m) - ((n.val - 1 : Nat) : ZMod m))).val =
          n.val - 1 := by
      simpa [d] using hdval
    simp_all [endpoint1DescRank?]
    exact endpointLabelOfNat?_eq_some_of_val (by omega)
  · let d := n.val - (m + 1)
    have hdlt : d < m := by
      have hnlt : n.val < 2 * m := n.isLt
      omega
    have hdval :
        ((2 : ZMod m) - ((2 : ZMod m) - (d : ZMod m))).val = d :=
      zmod_two_sub_two_sub_val hdlt
    have hdval' :
        ((2 : ZMod m) -
            ((2 : ZMod m) - ((n.val - (m + 1) : Nat) : ZMod m))).val =
          n.val - (m + 1) := by
      simpa [d] using hdval
    simp_all [endpoint1DescRank?]
    exact endpointLabelOfNat?_eq_some_of_val (by omega)
  · let d := n.val - (m + 1)
    have hdlt : d < m := by
      have hnlt : n.val < 2 * m := n.isLt
      omega
    have hdval :
        ((2 : ZMod m) - ((2 : ZMod m) - (d : ZMod m))).val = d :=
      zmod_two_sub_two_sub_val hdlt
    have hdval' :
        ((2 : ZMod m) -
            ((2 : ZMod m) - ((n.val - (m + 1) : Nat) : ZMod m))).val =
          n.val - (m + 1) := by
      simpa [d] using hdval
    simp_all [endpoint1DescRank?]
    exact endpointLabelOfNat?_eq_some_of_val (by omega)

set_option maxHeartbeats 2000000 in
theorem endpoint2DescRank?_endpoint2Desc {m : Nat} [NeZero m]
    (hmEven : Even m) (hm : 6 ≤ m) (n : EndpointLabel m) :
    endpoint2DescRank? m (endpoint2Desc m n) = some n := by
  simp only [endpoint2Desc]
  split_ifs with h1 h2 h3 h4 h5 h6
  · simp [endpoint2DescRank?]
    exact endpointLabelOfNat?_eq_some_of_val h1
  · simp [endpoint2DescRank?]
    exact endpointLabelOfNat?_eq_some_of_val h2
  · simp [endpoint2DescRank?]
    exact endpointLabelOfNat?_eq_some_of_val h3
  · let d := n.val - 2
    have hn2 : 2 ≤ n.val := by omega
    have hdlt : d < m := by omega
    have hdval :
        (((4 : ZMod m) + (d : ZMod m)) - (4 : ZMod m)).val = d :=
      zmod_four_add_sub_four_val hdlt
    have hdval' :
        (((4 : ZMod m) + ((n.val - 2 : Nat) : ZMod m)) -
            (4 : ZMod m)).val = n.val - 2 := by
      simpa [d] using hdval
    simp_all [endpoint2DescRank?]
  · let d := n.val - 2
    have hn2 : 2 ≤ n.val := by omega
    have hdlt : d < m := by omega
    have hdval :
        (((4 : ZMod m) + (d : ZMod m)) - (4 : ZMod m)).val = d :=
      zmod_four_add_sub_four_val hdlt
    have hdval' :
        (((4 : ZMod m) + ((n.val - 2 : Nat) : ZMod m)) -
            (4 : ZMod m)).val = n.val - 2 := by
      simpa [d] using hdval
    have hr2 : (4 : ZMod m) + (d : ZMod m) ≠ (2 : ZMod m) := by
      intro h
      have hd' := four_add_natCast_eq_two_forces (m := m) (d := d) hm hdlt h
      have hpar : parityEven d = true := by
        rw [hd']
        exact parityEven_sub_two_of_even hmEven (by omega)
      have hpar' : parityEven (n.val - 2) = true := by
        simpa [d] using hpar
      rw [hpar'] at h5
      simp at h5
    have hr2' :
        (4 : ZMod m) + ((n.val - 2 : Nat) : ZMod m) ≠ (2 : ZMod m) := by
      simpa [d] using hr2
    simp_all [endpoint2DescRank?]
  · let d := n.val - (m + 2)
    have hdlt : d < m := by
      have hnlt : n.val < 2 * m := n.isLt
      omega
    have hdlt_strong : d < m - 2 := by
      have hnlt : n.val < 2 * m := n.isLt
      omega
    have hdval :
        (((4 : ZMod m) + (d : ZMod m)) - (4 : ZMod m)).val = d :=
      zmod_four_add_sub_four_val hdlt
    have hdval' :
        (((4 : ZMod m) + ((n.val - (m + 2) : Nat) : ZMod m)) -
            (4 : ZMod m)).val = n.val - (m + 2) := by
      simpa [d] using hdval
    have hr2 : (4 : ZMod m) + (d : ZMod m) ≠ (2 : ZMod m) := by
      intro h
      have hd' := four_add_natCast_eq_two_forces (m := m) (d := d) hm hdlt h
      omega
    have hr2' :
        (4 : ZMod m) + ((n.val - (m + 2) : Nat) : ZMod m) ≠
          (2 : ZMod m) := by
      simpa [d] using hr2
    simp_all [endpoint2DescRank?]
    exact endpointLabelOfNat?_eq_some_of_val (by omega)
  · let d := n.val - (m + 2)
    have hdlt : d < m := by
      have hnlt : n.val < 2 * m := n.isLt
      omega
    have hdval :
        (((4 : ZMod m) + (d : ZMod m)) - (4 : ZMod m)).val = d :=
      zmod_four_add_sub_four_val hdlt
    have hdval' :
        (((4 : ZMod m) + ((n.val - (m + 2) : Nat) : ZMod m)) -
            (4 : ZMod m)).val = n.val - (m + 2) := by
      simpa [d] using hdval
    simp_all [endpoint2DescRank?]
    exact endpointLabelOfNat?_eq_some_of_val (by omega)

theorem endpoint0Desc_injective_of_six_le {m : Nat} [NeZero m]
    (hm : 6 ≤ m) :
    Function.Injective (endpoint0Desc m) := by
  intro n k h
  have hn := endpoint0DescRank?_endpoint0Desc hm n
  have hk := endpoint0DescRank?_endpoint0Desc hm k
  have hsome : some n = some k := by
    rw [← hn, h, hk]
  exact Option.some.inj hsome

theorem endpoint1Desc_injective_of_six_le {m : Nat} [NeZero m]
    (hm : 6 ≤ m) :
    Function.Injective (endpoint1Desc m) := by
  intro n k h
  have hn := endpoint1DescRank?_endpoint1Desc hm n
  have hk := endpoint1DescRank?_endpoint1Desc hm k
  have hsome : some n = some k := by
    rw [← hn, h, hk]
  exact Option.some.inj hsome

theorem endpoint2Desc_injective_of_even_six_le {m : Nat} [NeZero m]
    (hmEven : Even m) (hm : 6 ≤ m) :
    Function.Injective (endpoint2Desc m) := by
  intro n k h
  have hn := endpoint2DescRank?_endpoint2Desc hmEven hm n
  have hk := endpoint2DescRank?_endpoint2Desc hmEven hm k
  have hsome : some n = some k := by
    rw [← hn, h, hk]
  exact Option.some.inj hsome

theorem endpointDesc_injective_of_even_six_le {m : Nat} [NeZero m]
    (hmEven : Even m) (hm : 6 ≤ m) (c : TorusColor 3) :
    Function.Injective (endpointDesc m c) := by
  fin_cases c
  · exact endpoint0Desc_injective_of_six_le hm
  · exact endpoint1Desc_injective_of_six_le hm
  · exact endpoint2Desc_injective_of_even_six_le hmEven hm

theorem endpoint0Point_eq_descPoint {m : Nat} [NeZero m] (n : EndpointLabel m) :
    endpoint0Point m n = endpointDescPoint (m := m) 0 (endpoint0Desc m n) := by
  simp only [endpoint0Point, endpoint0Desc]
  split_ifs
  all_goals
    ext <;>
      simp [endpointDescPoint, D3TerminalA2Parametric.terminalEndpointA,
        D3TerminalA2Parametric.terminalEndpointB] <;>
      try ring_nf
  all_goals
    exfalso
    have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    have hnlt : n.val < 2 * m := n.isLt
    omega

theorem endpoint1Point_eq_descPoint {m : Nat} [NeZero m] (n : EndpointLabel m) :
    endpoint1Point m n = endpointDescPoint (m := m) 1 (endpoint1Desc m n) := by
  simp only [endpoint1Point, endpoint1Desc]
  split_ifs
  all_goals
    ext <;>
      simp [endpointDescPoint, D3TerminalA2Parametric.terminalEndpointA,
        D3TerminalA2Parametric.terminalEndpointB] <;>
      ring_nf

theorem endpoint2Point_eq_descPoint {m : Nat} [NeZero m] (n : EndpointLabel m) :
    endpoint2Point m n = endpointDescPoint (m := m) 2 (endpoint2Desc m n) := by
  simp only [endpoint2Point, endpoint2Desc]
  split_ifs
  all_goals
    ext <;>
      simp [endpointDescPoint, D3TerminalA2Parametric.terminalEndpointA,
        D3TerminalA2Parametric.terminalEndpointB] <;>
      ring_nf

theorem endpointPoint_eq_descPoint {m : Nat} [NeZero m]
    (c : TorusColor 3) (n : EndpointLabel m) :
    endpointPoint m c n =
      endpointDescPoint (m := m) c (endpointDesc m c n) := by
  fin_cases c
  · exact endpoint0Point_eq_descPoint n
  · exact endpoint1Point_eq_descPoint n
  · exact endpoint2Point_eq_descPoint n

theorem endpoint0Desc_valid_of_label {m : Nat} [NeZero m]
    (hm : 6 ≤ m) (n : EndpointLabel m) :
    endpointDescValid (m := m) 0 (endpoint0Desc m n) := by
  simp only [endpoint0Desc]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · trivial
  · simp [endpointDescValid, endpointCollisionIndex]
    intro h
    have h' : ((1 : Nat) : ZMod m) = ((2 : Nat) : ZMod m) := by
      simpa using h
    exact (zmod_natCast_ne_of_lt (m := m) (a := 1) (b := 2)
      (by omega) (by omega) (by omega)) h'
  · trivial
  · simp [endpointDescValid, endpointCollisionIndex]
    intro h
    have h' : ((1 : Nat) : ZMod m) = ((2 : Nat) : ZMod m) := by
      simpa using h
    exact (zmod_natCast_ne_of_lt (m := m) (a := 1) (b := 2)
      (by omega) (by omega) (by omega)) h'
  · simp [endpointDescValid, endpointCollisionIndex]
    exact negNat_ne_two_of_lt_m_sub_two hm h5
  · simp [endpointDescValid, endpointCollisionIndex]
    exact negNat_ne_two_of_lt_m_sub_two hm h5
  · simp [endpointDescValid, endpointCollisionIndex]
    have hd : n.val - m < m - 2 := by
      have hnlt2 : n.val < 2 * m - 2 := h7
      omega
    exact negNat_ne_two_of_lt_m_sub_two hm hd
  · simp [endpointDescValid, endpointCollisionIndex]
    have hd : n.val - m < m - 2 := by
      have hnlt2 : n.val < 2 * m - 2 := h7
      omega
    exact negNat_ne_two_of_lt_m_sub_two hm hd
  · simp [endpointDescValid, endpointCollisionIndex]
    intro h
    have h' : ((0 : Nat) : ZMod m) = ((2 : Nat) : ZMod m) := by
      simpa using h
    exact (zmod_natCast_ne_of_lt (m := m) (a := 0) (b := 2)
      (by omega) (by omega) (by omega)) h'

theorem endpoint1Desc_valid_of_label {m : Nat} [NeZero m]
    (hm : 6 ≤ m) (n : EndpointLabel m) :
    endpointDescValid (m := m) 1 (endpoint1Desc m n) := by
  simp only [endpoint1Desc]
  split_ifs with h1 h2 h3 h4 h5
  · trivial
  · trivial
  · simp [endpointDescValid, endpointCollisionIndex]
    have hd : n.val - 1 < m - 1 := by omega
    exact two_sub_natCast_ne_three_of_lt_m_sub_one hm hd
  · simp [endpointDescValid, endpointCollisionIndex]
    have hd : n.val - 1 < m - 1 := by omega
    exact two_sub_natCast_ne_three_of_lt_m_sub_one hm hd
  · simp [endpointDescValid, endpointCollisionIndex]
    have hd : n.val - (m + 1) < m - 1 := by
      have hnlt : n.val < 2 * m := n.isLt
      omega
    exact two_sub_natCast_ne_three_of_lt_m_sub_one hm hd
  · simp [endpointDescValid, endpointCollisionIndex]
    have hd : n.val - (m + 1) < m - 1 := by
      have hnlt : n.val < 2 * m := n.isLt
      omega
    exact two_sub_natCast_ne_three_of_lt_m_sub_one hm hd

theorem endpoint2Desc_valid_of_label {m : Nat} [NeZero m]
    (hm : 6 ≤ m) (n : EndpointLabel m) :
    endpointDescValid (m := m) 2 (endpoint2Desc m n) := by
  simp only [endpoint2Desc]
  split_ifs with h1 h2 h3 h4 h5 h6
  · simp [endpointDescValid, endpointCollisionIndex]
    intro h
    have h' : ((2 : Nat) : ZMod m) = ((3 : Nat) : ZMod m) := by
      simpa using h
    exact (zmod_natCast_ne_of_lt (m := m) (a := 2) (b := 3)
      (by omega) (by omega) (by omega)) h'
  · trivial
  · trivial
  · simp [endpointDescValid, endpointCollisionIndex]
    have hd : n.val - 2 < m - 1 := by omega
    exact four_add_natCast_ne_three_of_lt_m_sub_one hm hd
  · simp [endpointDescValid, endpointCollisionIndex]
    have hd : n.val - 2 < m - 1 := by omega
    exact four_add_natCast_ne_three_of_lt_m_sub_one hm hd
  · simp [endpointDescValid, endpointCollisionIndex]
    have hd : n.val - (m + 2) < m - 1 := by
      have hnlt : n.val < 2 * m := n.isLt
      omega
    exact four_add_natCast_ne_three_of_lt_m_sub_one hm hd
  · simp [endpointDescValid, endpointCollisionIndex]
    have hd : n.val - (m + 2) < m - 1 := by
      have hnlt : n.val < 2 * m := n.isLt
      omega
    exact four_add_natCast_ne_three_of_lt_m_sub_one hm hd

theorem endpointDesc_valid_of_label {m : Nat} [NeZero m]
    (hm : 6 ≤ m) (c : TorusColor 3) (n : EndpointLabel m) :
    endpointDescValid (m := m) c (endpointDesc m c n) := by
  fin_cases c
  · exact endpoint0Desc_valid_of_label hm n
  · exact endpoint1Desc_valid_of_label hm n
  · exact endpoint2Desc_valid_of_label hm n

/-- Valid endpoint descriptors have no point collisions for `m ≥ 6`.  This is
the point-level no-collision layer; the remaining parametric injectivity work is
to show that the closed-form rank decoder never repeats a valid descriptor. -/
theorem endpointDescPoint_injective_of_valid {m : Nat} [NeZero m]
    (hm : 6 ≤ m) (c : TorusColor 3) :
    ∀ {x y : EndpointDesc m}, endpointDescValid (m := m) c x →
      endpointDescValid (m := m) c y →
      endpointDescPoint (m := m) c x = endpointDescPoint (m := m) c y →
      x = y := by
  intro x y hx hy h
  cases x <;> cases y
  case A.A r s =>
    apply congrArg EndpointDesc.A
    exact terminalEndpointA_injective c (by simpa [endpointDescPoint] using h)
  case A.B r s =>
    exfalso
    fin_cases c
    · have hc := endpoint0_generic_AB_collision
        (by
          simpa [endpointDescPoint, D3TerminalA2Parametric.terminalEndpointA,
            D3TerminalA2Parametric.terminalEndpointB] using h)
      exact hx (by simpa [endpointDescValid, endpointCollisionIndex] using hc.1)
    · have hc := endpoint1_generic_AB_collision
        (by
          simpa [endpointDescPoint, D3TerminalA2Parametric.terminalEndpointA,
            D3TerminalA2Parametric.terminalEndpointB] using h)
      exact hx (by simpa [endpointDescValid, endpointCollisionIndex] using hc.1)
    · have hc := endpoint2_generic_AB_collision
        (by
          simpa [endpointDescPoint, D3TerminalA2Parametric.terminalEndpointA,
            D3TerminalA2Parametric.terminalEndpointB] using h)
      exact hx (by simpa [endpointDescValid, endpointCollisionIndex] using hc.1)
  case A.Eplus r =>
    fin_cases c <;> exfalso <;>
      simp [endpointDescPoint, endpointDescValid, endpointCollisionIndex,
        D3TerminalA2Parametric.terminalEndpointA] at hx hy h
    · exact hx h.1
    · exact hx h.2
    · exact (zmod_small_ne_of_six_le (m := m) (a := 1) (b := 2) hm
        (by omega) (by omega) (by omega)) (by simpa using h.1)
  case A.Eminus r =>
    fin_cases c <;> exfalso <;>
      simp [endpointDescPoint, endpointDescValid, endpointCollisionIndex,
        D3TerminalA2Parametric.terminalEndpointA] at hx hy h
    · exact hx h.1
    · exact hx h.2
    · exact (zmod_small_ne_of_six_le (m := m) (a := 1) (b := 0) hm
        (by omega) (by omega) (by omega)) (by simpa using h.1)
  case B.A r s =>
    exfalso
    fin_cases c
    · have hc := endpoint0_generic_AB_collision
        (by
          simpa [endpointDescPoint, D3TerminalA2Parametric.terminalEndpointA,
            D3TerminalA2Parametric.terminalEndpointB] using h.symm)
      exact hx (by simpa [endpointDescValid, endpointCollisionIndex] using hc.2)
    · have hc := endpoint1_generic_AB_collision
        (by
          simpa [endpointDescPoint, D3TerminalA2Parametric.terminalEndpointA,
            D3TerminalA2Parametric.terminalEndpointB] using h.symm)
      exact hx (by simpa [endpointDescValid, endpointCollisionIndex] using hc.2)
    · have hc := endpoint2_generic_AB_collision
        (by
          simpa [endpointDescPoint, D3TerminalA2Parametric.terminalEndpointA,
            D3TerminalA2Parametric.terminalEndpointB] using h.symm)
      exact hx (by simpa [endpointDescValid, endpointCollisionIndex] using hc.2)
  case B.B r s =>
    apply congrArg EndpointDesc.B
    exact terminalEndpointB_injective c (by simpa [endpointDescPoint] using h)
  case B.Eplus r =>
    fin_cases c <;> exfalso <;>
      simp [endpointDescPoint, endpointDescValid, endpointCollisionIndex,
        D3TerminalA2Parametric.terminalEndpointB] at hx hy h
    · exact hx h.1
    · exact hx h.2
    · exact (zmod_small_ne_of_six_le (m := m) (a := 2) (b := 1) hm
        (by omega) (by omega) (by omega)) (by simpa using h.2)
  case B.Eminus r =>
    fin_cases c <;> exfalso <;>
      simp [endpointDescPoint, endpointDescValid, endpointCollisionIndex,
        D3TerminalA2Parametric.terminalEndpointB] at hx hy h
    · exact hx h.1
    · exact hx h.2
    · exact (zmod_small_ne_of_six_le (m := m) (a := 2) (b := 3) hm
        (by omega) (by omega) (by omega)) (by simpa using h.2)
  case Eplus.A r =>
    fin_cases c <;> exfalso <;>
      simp [endpointDescPoint, endpointDescValid, endpointCollisionIndex,
        D3TerminalA2Parametric.terminalEndpointA] at hx hy h
    · exact hy h.1.symm
    · exact hy h.2.symm
    · exact (zmod_small_ne_of_six_le (m := m) (a := 2) (b := 1) hm
        (by omega) (by omega) (by omega)) (by simpa using h.1)
  case Eplus.B r =>
    fin_cases c <;> exfalso <;>
      simp [endpointDescPoint, endpointDescValid, endpointCollisionIndex,
        D3TerminalA2Parametric.terminalEndpointB] at hx hy h
    · exact hy h.1.symm
    · exact hy h.2.symm
    · exact (zmod_small_ne_of_six_le (m := m) (a := 1) (b := 2) hm
        (by omega) (by omega) (by omega)) (by simpa using h.2)
  case Eplus.Eplus =>
    rfl
  case Eplus.Eminus =>
    fin_cases c <;> exfalso <;> simp [endpointDescPoint] at h
    · exact (zmod_small_ne_of_six_le (m := m) (a := 3) (b := 1) hm
        (by omega) (by omega) (by omega)) (by simpa using h)
    · exact (zmod_small_ne_of_six_le (m := m) (a := 0) (b := 2) hm
        (by omega) (by omega) (by omega)) (by simpa using h)
    · exact (zmod_small_ne_of_six_le (m := m) (a := 2) (b := 0) hm
        (by omega) (by omega) (by omega)) (by simpa using h.1)
  case Eminus.A r =>
    fin_cases c <;> exfalso <;>
      simp [endpointDescPoint, endpointDescValid, endpointCollisionIndex,
        D3TerminalA2Parametric.terminalEndpointA] at hx hy h
    · exact hy h.1.symm
    · exact hy h.2.symm
    · exact (zmod_small_ne_of_six_le (m := m) (a := 0) (b := 1) hm
        (by omega) (by omega) (by omega)) (by simpa using h.1)
  case Eminus.B r =>
    fin_cases c <;> exfalso <;>
      simp [endpointDescPoint, endpointDescValid, endpointCollisionIndex,
        D3TerminalA2Parametric.terminalEndpointB] at hx hy h
    · exact hy h.1.symm
    · exact hy h.2.symm
    · exact (zmod_small_ne_of_six_le (m := m) (a := 3) (b := 2) hm
        (by omega) (by omega) (by omega)) (by simpa using h.2)
  case Eminus.Eplus =>
    fin_cases c <;> exfalso <;> simp [endpointDescPoint] at h
    · exact (zmod_small_ne_of_six_le (m := m) (a := 1) (b := 3) hm
        (by omega) (by omega) (by omega)) (by simpa using h)
    · exact (zmod_small_ne_of_six_le (m := m) (a := 2) (b := 0) hm
        (by omega) (by omega) (by omega)) (by simpa using h)
    · exact (zmod_small_ne_of_six_le (m := m) (a := 0) (b := 2) hm
        (by omega) (by omega) (by omega)) (by simpa using h.1)
  case Eminus.Eminus =>
    rfl

/-- The full endpoint list is injective once the closed-form descriptor decoder
is injective.  This separates the point-collision arithmetic from the remaining
rank/parity arithmetic. -/
theorem endpointPoint_injective_of_desc_injective {m : Nat} [NeZero m]
    (hm : 6 ≤ m) (c : TorusColor 3)
    (hdesc : Function.Injective (endpointDesc m c)) :
    Function.Injective (endpointPoint m c) := by
  intro n k h
  apply hdesc
  apply endpointDescPoint_injective_of_valid hm c
  · exact endpointDesc_valid_of_label hm c n
  · exact endpointDesc_valid_of_label hm c k
  · simpa [← endpointPoint_eq_descPoint] using h

theorem endpointPoint_injective_of_even_six_le {m : Nat} [NeZero m]
    (hmEven : Even m) (hm : 6 ≤ m) (c : TorusColor 3) :
    Function.Injective (endpointPoint m c) :=
  endpointPoint_injective_of_desc_injective hm c
    (endpointDesc_injective_of_even_six_le hmEven hm c)

/-- For every odd `m ≥ 6`, color 2 repeats the endpoint `(0,2)` at rank labels
`0` and `m`. -/
theorem endpoint2Point_odd_collision {m : Nat} [NeZero m]
    (hmOdd : Odd m) (hm : 6 ≤ m) :
    endpoint2Point m (⟨0, by omega⟩ : EndpointLabel m) =
      endpoint2Point m (⟨m, by omega⟩ : EndpointLabel m) := by
  have hpar : parityEven (m - 2) = false :=
    parityEven_sub_two_of_odd hmOdd (by omega)
  have hm0 : m ≠ 0 := by omega
  have hm1 : m ≠ 1 := by omega
  simp [endpoint2Point, hpar, hm0, hm1]
  have hcast : ((m - 2 : Nat) : ZMod m) = -(2 : ZMod m) :=
    natCast_sub_eq_neg_natCast (m := m) (a := 2) (by omega)
  rw [hcast]
  ring

theorem endpointPoint_odd_color2_not_injective {m : Nat} [NeZero m]
    (hmOdd : Odd m) (hm : 6 ≤ m) :
    ¬ Function.Injective (endpointPoint m (2 : TorusColor 3)) := by
  intro h
  have hneq :
      (⟨0, by omega⟩ : EndpointLabel m) ≠ ⟨m, by omega⟩ := by
    intro hfin
    have hval := congrArg Fin.val hfin
    simp at hval
    omega
  exact hneq (h (endpoint2Point_odd_collision hmOdd hm))

/-- Odd moduli are not covered by the generic endpoint rank list.  Already at
`m = 7`, color 2 repeats the endpoint `(0,2)` at rank labels `0` and `7`.
This records why the parametric no-collision theorem has the paper's even
modulus hypothesis. -/
theorem endpoint2Point_m7_collision :
    endpoint2Point 7 (⟨0, by decide⟩ : EndpointLabel 7) =
      endpoint2Point 7 (⟨7, by decide⟩ : EndpointLabel 7) := by
  decide

theorem endpointPoint_m7_color2_not_injective :
    ¬ Function.Injective (endpointPoint 7 (2 : TorusColor 3)) := by
  intro h
  have hneq : (⟨0, by decide⟩ : EndpointLabel 7) ≠ ⟨7, by decide⟩ := by
    decide
  exact hneq (h endpoint2Point_m7_collision)

/-- The first generic modulus: all three inverse rank lists have no collision. -/
theorem endpointPoint_m6_injective (c : TorusColor 3) :
    Function.Injective (endpointPoint 6 c) := by
  fin_cases c <;> decide

/-- A second generic sanity check, beyond the small parent `m = 6`. -/
theorem endpointPoint_m8_injective (c : TorusColor 3) :
    Function.Injective (endpointPoint 8 c) := by
  fin_cases c <;> decide

/-- The image of a closed-form endpoint rank list inside the terminal carrier
state space.  This is the active endpoint set once the parametric no-collision
lemma is supplied. -/
abbrev EndpointImage (m : Nat) [NeZero m] (c : TorusColor 3) :=
  { q : TerminalQ m // q ∈ Set.range (endpointPoint m c) }

/-- An injective endpoint list identifies rank labels with the corresponding
endpoint image subtype. -/
noncomputable def endpointImageEquiv (m : Nat) [NeZero m] (c : TorusColor 3)
    (hinj : Function.Injective (endpointPoint m c)) :
    EndpointLabel m ≃ EndpointImage m c where
  toFun n := ⟨endpointPoint m c n, ⟨n, rfl⟩⟩
  invFun q := Classical.choose q.property
  left_inv n := by
    apply hinj
    exact Classical.choose_spec
      (show endpointPoint m c n ∈ Set.range (endpointPoint m c) from ⟨n, rfl⟩)
  right_inv q := by
    apply Subtype.ext
    exact Classical.choose_spec q.property

/-- The image-subtype successor induced by the endpoint rank successor.  The
future paper-rank step should prove that the concrete endpoint successor `h_i`
is pointwise equal to this map. -/
noncomputable def endpointImageSucc (m : Nat) [NeZero m] (c : TorusColor 3)
    (hinj : Function.Injective (endpointPoint m c)) :
    EndpointImage m c → EndpointImage m c :=
  let e := endpointImageEquiv m c hinj
  fun q => e (endpointRankSucc m (e.symm q))

/-- Once the endpoint list is injective, the induced successor on its image is a
single cycle.  This isolates the remaining H1a work to identifying the paper
endpoint map with `endpointImageSucc`, then applying the interval-splice lift
from active endpoints to the full terminal carrier. -/
theorem endpointImageSucc_singleCycle {m : Nat} [NeZero m] (c : TorusColor 3)
    (hinj : Function.Injective (endpointPoint m c)) :
    Shared.IsSingleCycleMap (endpointImageSucc m c hinj) := by
  let e := endpointImageEquiv m c hinj
  exact Shared.single_cycle_of_equiv_conj e
    (endpointImageSucc m c hinj)
    (endpointRankSucc m)
    endpointRankSucc_singleCycle
    (by
      intro n
      simp [endpointImageSucc, e])

/-- On a listed endpoint, the image-subtype successor has the expected raw
value. -/
theorem endpointImageSucc_apply_endpointPoint {m : Nat} [NeZero m]
    (c : TorusColor 3) (hinj : Function.Injective (endpointPoint m c))
    (n : EndpointLabel m) :
    (endpointImageSucc m c hinj
      ⟨endpointPoint m c n, ⟨n, rfl⟩⟩).val =
      endpointPoint m c (endpointRankSucc m n) := by
  let e := endpointImageEquiv m c hinj
  change endpointPoint m c (endpointRankSucc m
    (e.symm (e n))) = endpointPoint m c (endpointRankSucc m n)
  have hleft : e.symm (e n) = n := e.left_inv n
  rw [hleft]

/-- Restrict a raw terminal-state map to the endpoint image, provided it
preserves that image. -/
noncomputable def endpointImageMapOf {m : Nat} [NeZero m] (c : TorusColor 3)
    (step : TerminalQ m → TerminalQ m)
    (hclosed : ∀ q : EndpointImage m c,
      step q.val ∈ Set.range (endpointPoint m c)) :
    EndpointImage m c → EndpointImage m c :=
  fun q => ⟨step q.val, hclosed q⟩

/-- A pointwise rank-step table automatically proves that the raw step preserves
the endpoint image. -/
theorem endpointImage_closed_of_rank_step {m : Nat} [NeZero m]
    (c : TorusColor 3) (step : TerminalQ m → TerminalQ m)
    (hstep : ∀ n : EndpointLabel m,
      step (endpointPoint m c n) =
        endpointPoint m c (endpointRankSucc m n)) :
    ∀ q : EndpointImage m c,
      step q.val ∈ Set.range (endpointPoint m c) := by
  intro q
  rcases q.property with ⟨n, hn⟩
  refine ⟨endpointRankSucc m n, ?_⟩
  rw [← hn]
  exact (hstep n).symm

/-- The endpoint-image restriction built from only a pointwise rank-step table. -/
noncomputable def endpointImageMapOfRankStep {m : Nat} [NeZero m]
    (c : TorusColor 3) (step : TerminalQ m → TerminalQ m)
    (hstep : ∀ n : EndpointLabel m,
      step (endpointPoint m c n) =
        endpointPoint m c (endpointRankSucc m n)) :
    EndpointImage m c → EndpointImage m c :=
  endpointImageMapOf c step (endpointImage_closed_of_rank_step c step hstep)

/-- If a raw step advances every listed endpoint by one rank, then its
restriction to the endpoint image is exactly the rank-induced successor. -/
theorem endpointImageMapOf_eq_imageSucc_of_rank_step {m : Nat} [NeZero m]
    (c : TorusColor 3) (step : TerminalQ m → TerminalQ m)
    (hclosed : ∀ q : EndpointImage m c,
      step q.val ∈ Set.range (endpointPoint m c))
    (hinj : Function.Injective (endpointPoint m c))
    (hstep : ∀ n : EndpointLabel m,
      step (endpointPoint m c n) =
        endpointPoint m c (endpointRankSucc m n)) :
    endpointImageMapOf c step hclosed = endpointImageSucc m c hinj := by
  funext q
  rcases q.property with ⟨n, hn⟩
  have hq : q = ⟨endpointPoint m c n, ⟨n, rfl⟩⟩ := by
    apply Subtype.ext
    exact hn.symm
  rw [hq]
  apply Subtype.ext
  simp [endpointImageMapOf, endpointImageSucc_apply_endpointPoint, hstep]

/-- The endpoint-image cyclicity target reduced to the paper rank-step table:
prove only that the raw endpoint successor sends each listed endpoint to the
next listed endpoint. -/
theorem endpointImageMapOf_singleCycle_of_rank_step {m : Nat} [NeZero m]
    (c : TorusColor 3) (step : TerminalQ m → TerminalQ m)
    (hclosed : ∀ q : EndpointImage m c,
      step q.val ∈ Set.range (endpointPoint m c))
    (hinj : Function.Injective (endpointPoint m c))
    (hstep : ∀ n : EndpointLabel m,
      step (endpointPoint m c n) =
        endpointPoint m c (endpointRankSucc m n)) :
    Shared.IsSingleCycleMap (endpointImageMapOf c step hclosed) := by
  rw [endpointImageMapOf_eq_imageSucc_of_rank_step c step hclosed hinj hstep]
  exact endpointImageSucc_singleCycle c hinj

/-- Same as `endpointImageMapOf_singleCycle_of_rank_step`, with image closedness
derived automatically from the rank-step table. -/
theorem endpointImageMapOfRankStep_singleCycle {m : Nat} [NeZero m]
    (c : TorusColor 3) (step : TerminalQ m → TerminalQ m)
    (hinj : Function.Injective (endpointPoint m c))
    (hstep : ∀ n : EndpointLabel m,
      step (endpointPoint m c n) =
        endpointPoint m c (endpointRankSucc m n)) :
    Shared.IsSingleCycleMap (endpointImageMapOfRankStep c step hstep) :=
  endpointImageMapOf_singleCycle_of_rank_step c step
    (endpointImage_closed_of_rank_step c step hstep) hinj hstep

/-- Descriptor-level rank-step is enough to prove the raw pointwise endpoint
rank-step for the paper recurrence map.  The remaining finite/parity target is
therefore the equality involving `endpointDescSucc`, not a raw terminal-point
calculation. -/
theorem compressedEndpoint_rank_step_of_desc_rank_step {m : Nat} [NeZero m]
    (hm : 6 ≤ m)
    (rec : D3TerminalA2Parametric.TerminalA2EndpointRecurrence m)
    (c : TorusColor 3)
    (hdesc : ∀ n : EndpointLabel m,
      endpointDescSucc c (endpointDesc m c n) =
        endpointDesc m c (endpointRankSucc m n)) :
    ∀ n : EndpointLabel m,
      D3TerminalA2Parametric.terminalCompressedEndpointReturn
          (m := m) rec.exchange c (endpointPoint m c n) =
        endpointPoint m c (endpointRankSucc m n) := by
  intro n
  calc
    D3TerminalA2Parametric.terminalCompressedEndpointReturn
        (m := m) rec.exchange c (endpointPoint m c n)
        =
      D3TerminalA2Parametric.terminalCompressedEndpointReturn
        (m := m) rec.exchange c
        (endpointDescPoint (m := m) c (endpointDesc m c n)) := by
          rw [endpointPoint_eq_descPoint]
    _ = endpointDescPoint (m := m) c
          (endpointDescSucc c (endpointDesc m c n)) :=
        terminalCompressedEndpointReturn_endpointDescSucc rec c
          (endpointDesc m c n) (endpointDesc_valid_of_label hm c n)
    _ = endpointDescPoint (m := m) c
          (endpointDesc m c (endpointRankSucc m n)) := by
        rw [hdesc n]
    _ = endpointPoint m c (endpointRankSucc m n) := by
        rw [← endpointPoint_eq_descPoint]

/-- The H1a endpoint recurrence target in the names used by
`D3TerminalA2Parametric`: once the paper recurrence map is shown to advance the
closed-form rank list, it is cyclic on the active endpoint image. -/
theorem compressedEndpointImageMap_singleCycle_of_rank_step {m : Nat}
    [NeZero m]
    (rec : D3TerminalA2Parametric.TerminalA2EndpointRecurrence m)
    (c : TorusColor 3)
    (hinj : Function.Injective (endpointPoint m c))
    (hstep : ∀ n : EndpointLabel m,
      D3TerminalA2Parametric.terminalCompressedEndpointReturn
          (m := m) rec.exchange c (endpointPoint m c n) =
        endpointPoint m c (endpointRankSucc m n)) :
    Shared.IsSingleCycleMap
      (endpointImageMapOfRankStep c
        (D3TerminalA2Parametric.terminalCompressedEndpointReturn
          (m := m) rec.exchange c) hstep) :=
  endpointImageMapOfRankStep_singleCycle c
    (D3TerminalA2Parametric.terminalCompressedEndpointReturn
      (m := m) rec.exchange c) hinj hstep

/-- Even generic version of `endpointImageSucc_singleCycle`, with the endpoint
no-collision theorem already supplied.  This is the H1a state after the
endpoint no-collision bundle: for every even `m ≥ 6`, the closed-form endpoint
rank successor is cyclic on the endpoint image. -/
theorem endpointImageSucc_singleCycle_of_even_six_le {m : Nat} [NeZero m]
    (hmEven : Even m) (hm : 6 ≤ m) (c : TorusColor 3) :
    Shared.IsSingleCycleMap
      (endpointImageSucc m c
        (endpointPoint_injective_of_even_six_le hmEven hm c)) :=
  endpointImageSucc_singleCycle c
    (endpointPoint_injective_of_even_six_le hmEven hm c)

/-- Even generic endpoint-recurrence handoff.  After the concrete paper
recurrence map is shown to advance the closed-form endpoint rank list by one
step, cyclicity on the active endpoint image follows with no extra injectivity
argument. -/
theorem compressedEndpointImageMap_singleCycle_of_even_six_le_rank_step
    {m : Nat} [NeZero m]
    (hmEven : Even m) (hm : 6 ≤ m)
    (rec : D3TerminalA2Parametric.TerminalA2EndpointRecurrence m)
    (c : TorusColor 3)
    (hstep : ∀ n : EndpointLabel m,
      D3TerminalA2Parametric.terminalCompressedEndpointReturn
          (m := m) rec.exchange c (endpointPoint m c n) =
        endpointPoint m c (endpointRankSucc m n)) :
    Shared.IsSingleCycleMap
      (endpointImageMapOfRankStep c
        (D3TerminalA2Parametric.terminalCompressedEndpointReturn
          (m := m) rec.exchange c) hstep) :=
  compressedEndpointImageMap_singleCycle_of_rank_step rec c
    (endpointPoint_injective_of_even_six_le hmEven hm c) hstep

/-- Even generic endpoint-recurrence handoff reduced to the descriptor rank
table.  Once `endpointDescSucc` is shown to match `endpointRankSucc` on the
closed-form rank list, cyclicity on the active endpoint image follows. -/
theorem compressedEndpointImageMap_singleCycle_of_even_six_le_desc_rank_step
    {m : Nat} [NeZero m]
    (hmEven : Even m) (hm : 6 ≤ m)
    (rec : D3TerminalA2Parametric.TerminalA2EndpointRecurrence m)
    (c : TorusColor 3)
    (hdesc : ∀ n : EndpointLabel m,
      endpointDescSucc c (endpointDesc m c n) =
        endpointDesc m c (endpointRankSucc m n)) :
    Shared.IsSingleCycleMap
      (endpointImageMapOfRankStep c
        (D3TerminalA2Parametric.terminalCompressedEndpointReturn
          (m := m) rec.exchange c)
        (compressedEndpoint_rank_step_of_desc_rank_step hm rec c hdesc)) :=
  compressedEndpointImageMap_singleCycle_of_even_six_le_rank_step
    hmEven hm rec c
    (compressedEndpoint_rank_step_of_desc_rank_step hm rec c hdesc)

theorem endpointImageSucc_m6_singleCycle (c : TorusColor 3) :
    Shared.IsSingleCycleMap
      (endpointImageSucc 6 c (endpointPoint_m6_injective c)) :=
  endpointImageSucc_singleCycle c (endpointPoint_m6_injective c)

theorem endpointImageSucc_m8_singleCycle (c : TorusColor 3) :
    Shared.IsSingleCycleMap
      (endpointImageSucc 8 c (endpointPoint_m8_injective c)) :=
  endpointImageSucc_singleCycle c (endpointPoint_m8_injective c)

end TerminalA2EndpointRank
end V28Hard
end EvenV11
