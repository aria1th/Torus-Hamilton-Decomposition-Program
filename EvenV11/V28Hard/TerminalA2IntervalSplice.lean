import EvenV11.V28Hard.TerminalA2ActiveSet

/-!
# Terminal `A₂` interval splice (H1a)

This file closes the H1a carrier-cyclicity theorem: for every even modulus
`m ≥ 6` and every terminal color `c`, the collapsed terminal carrier
`F_c = terminalReturn c` is a single `m²`-cycle on `Q_m = (ℤ/m)²`.

The proof is the paper's interval-splice argument.  The active endpoint
rank list `endpointPoint m c : Fin (2m) → Q_m` cuts the carrier orbit into
`2m` straight fiber intervals: the interval with label `k` starts at the
exchange partner of the rank point `succ k`, walks along the fiber by
repeated `+Δ_c` steps (where the jump `η_c` is the identity, by the
active-set characterization), and ends with one `η_c` jump onto the head
of interval `succ k`.  Splicing the intervals along the single cycle
`endpointRankSucc` and covering every point of `Q_m` by the two
complementary intervals of its fiber yields one global cycle.

Together with the finite `m = 4` orbit certificate, this assembles
`TerminalA2CarrierCyclicityFamily`, the H1a obligation of `EvenV11.Main`.
-/

namespace EvenV11
namespace V28Hard
namespace TerminalA2IntervalSplice

open Shared
open TerminalA2LowMod
open D3TerminalA2Parametric
open TerminalA2EndpointRank
open TerminalA2RecurrenceInstance
open TerminalA2ActiveSet

/-! ## Abstract orbit-splice lemma -/

/-- Abstract interval splice: if a finite-state map `F` is cut into labelled
intervals — interval `l` starts at `head l`, has positive length `len l`, and
`F^[len l]` carries `head l` to `head (σ l)` — where the label successor `σ`
is a single cycle and every state is interior to some interval, then `F`
itself is a single cycle. -/
theorem single_cycle_of_interval_splice {X L : Type*} [Finite X]
    (F : X → X) (σ : L → L) (head : L → X) (len : L → ℕ)
    (hlen : ∀ l, 0 < len l)
    (htraverse : ∀ l, F^[len l] (head l) = head (σ l))
    (hσ : Shared.IsSingleCycleMap σ)
    (hcover : ∀ x : X, ∃ l : L, ∃ j : ℕ, j < len l ∧ F^[j] (head l) = x) :
    Shared.IsSingleCycleMap F := by
  have chain : ∀ (k : ℕ) (l : L), ∃ N : ℕ,
      F^[N] (head l) = head (σ^[k] l) := by
    intro k
    induction k with
    | zero => exact fun l => ⟨0, rfl⟩
    | succ k ih =>
        intro l
        obtain ⟨N, hN⟩ := ih l
        refine ⟨len (σ^[k] l) + N, ?_⟩
        rw [Function.iterate_add_apply, hN, htraverse,
          Function.iterate_succ_apply']
  have reach : ∀ l l' : L, ∃ N : ℕ, F^[N] (head l) = head l' := by
    intro l l'
    obtain ⟨k, hk⟩ := hσ.2 l l'
    obtain ⟨N, hN⟩ := chain k l
    exact ⟨N, by rw [hN, hk]⟩
  have hsurj : Function.Surjective F := by
    intro y
    obtain ⟨l, j, _hj, hy⟩ := hcover y
    cases j with
    | zero =>
        obtain ⟨l₀, hl₀⟩ := hσ.1.2 l
        refine ⟨F^[len l₀ - 1] (head l₀), ?_⟩
        have h1 : len l₀ = (len l₀ - 1) + 1 := by
          have := hlen l₀
          omega
        calc F (F^[len l₀ - 1] (head l₀))
            = F^[len l₀] (head l₀) := by
              conv_rhs => rw [h1]
              rw [Function.iterate_succ_apply']
          _ = head (σ l₀) := htraverse l₀
          _ = y := by rw [hl₀]; exact hy
    | succ j =>
        exact ⟨F^[j] (head l), by
          rw [Function.iterate_succ_apply'] at hy; exact hy⟩
  have hinj : Function.Injective F :=
    Finite.injective_iff_surjective.mpr hsurj
  refine ⟨⟨hinj, hsurj⟩, ?_⟩
  intro x y
  obtain ⟨l, j, hj, hx⟩ := hcover x
  obtain ⟨l', j', _hj', hy⟩ := hcover y
  have hstep1 : F^[len l - j] x = head (σ l) := by
    rw [← hx, ← Function.iterate_add_apply]
    have hsum : len l - j + j = len l := by omega
    rw [hsum, htraverse]
  obtain ⟨N, hN⟩ := reach (σ l) l'
  refine ⟨j' + (N + (len l - j)), ?_⟩
  rw [Function.iterate_add_apply, Function.iterate_add_apply, hstep1, hN,
    hy]

/-! ## Small `ZMod` toolkit -/

private theorem natCast_inj_of_lt {m a b : ℕ} [NeZero m]
    (ha : a < m) (hb : b < m)
    (h : (a : ZMod m) = (b : ZMod m)) : a = b := by
  have hmod := (ZMod.natCast_eq_natCast_iff a b m).mp h
  exact Nat.ModEq.eq_of_lt_of_lt hmod ha hb

private theorem natCast_ne_of_lt {m a b : ℕ} [NeZero m]
    (ha : a < m) (hb : b < m) (hne : a ≠ b) :
    (a : ZMod m) ≠ (b : ZMod m) :=
  fun h => hne (natCast_inj_of_lt ha hb h)

private theorem zNe02 {m : ℕ} [NeZero m] (hm : 6 ≤ m) :
    (0 : ZMod m) ≠ 2 := by
  have h := natCast_ne_of_lt (m := m) (a := 0) (b := 2)
    (by omega) (by omega) (by omega)
  exact_mod_cast h

private theorem zNe13 {m : ℕ} [NeZero m] (hm : 6 ≤ m) :
    (1 : ZMod m) ≠ 3 := by
  have h := natCast_ne_of_lt (m := m) (a := 1) (b := 3)
    (by omega) (by omega) (by omega)
  exact_mod_cast h

private theorem pair_ne_left {m : ℕ} {x y a b : ZMod m} (h : x ≠ a) :
    ((x, y) : TerminalQ m) ≠ (a, b) :=
  fun he => h (congrArg Prod.fst he)

/-! ## Per-color fiber geometry -/

/-- Along-fiber coordinate: the component advanced by `+Δ_c`. -/
private def phi {m : ℕ} : TorusColor 3 → TerminalQ m → ZMod m
  | 0, z => z.2
  | 1, z => z.1
  | _, z => z.1

private theorem phi_step {m : ℕ} (c : TorusColor 3) (z : TerminalQ m) :
    phi c (z + terminalDelta (m := m) c) = phi c z + 1 := by
  fin_cases c
  · change (z + terminalDelta (m := m) 0).2 = z.2 + 1
    rfl
  · change (z + terminalDelta (m := m) 1).1 = z.1 + 1
    rfl
  · change (z + terminalDelta (m := m) 2).1 = z.1 + 1
    rfl

private theorem fiber_step {m : ℕ} (c : TorusColor 3) (z : TerminalQ m) :
    terminalFiberLabel c (z + terminalDelta (m := m) c) =
      terminalFiberLabel c z := by
  fin_cases c
  · change z.1 + (0 : ZMod m) = z.1
    ring
  · change z.2 + (0 : ZMod m) = z.2
    ring
  · change z.1 + 1 + (z.2 + (-1)) = z.1 + z.2
    ring

private theorem point_eq_of_fiber_phi {m : ℕ} (c : TorusColor 3)
    {z w : TerminalQ m}
    (hfib : terminalFiberLabel c z = terminalFiberLabel c w)
    (hphi : phi c z = phi c w) : z = w := by
  fin_cases c
  · exact Prod.ext hfib hphi
  · exact Prod.ext hphi hfib
  · refine Prod.ext hphi ?_
    have h2 : z.1 + z.2 = w.1 + w.2 := hfib
    have h1 : z.1 = w.1 := hphi
    linear_combination h2 - h1

private theorem phi_add_nsmul {m : ℕ} (c : TorusColor 3) (z : TerminalQ m)
    (j : ℕ) :
    phi c (z + j • terminalDelta (m := m) c) = phi c z + (j : ZMod m) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hsum : z + (j + 1) • terminalDelta (m := m) c =
          z + j • terminalDelta (m := m) c + terminalDelta (m := m) c := by
        rw [succ_nsmul, ← add_assoc]
      rw [hsum, phi_step, ih]
      push_cast
      ring

private theorem fiber_add_nsmul {m : ℕ} (c : TorusColor 3)
    (z : TerminalQ m) (j : ℕ) :
    terminalFiberLabel c (z + j • terminalDelta (m := m) c) =
      terminalFiberLabel c z := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hsum : z + (j + 1) • terminalDelta (m := m) c =
          z + j • terminalDelta (m := m) c + terminalDelta (m := m) c := by
        rw [succ_nsmul, ← add_assoc]
      rw [hsum, fiber_step, ih]

/-- Walking by the along-fiber distance reconstructs the target point. -/
private theorem add_val_smul_delta {m : ℕ} [NeZero m] (c : TorusColor 3)
    {w y : TerminalQ m}
    (hfib : terminalFiberLabel c w = terminalFiberLabel c y) :
    y + ((phi c w - phi c y).val) • terminalDelta (m := m) c = w := by
  apply point_eq_of_fiber_phi c
  · rw [fiber_add_nsmul]
    exact hfib.symm
  · rw [phi_add_nsmul, ZMod.natCast_zmod_val]
    ring

/-! ## Exchange involution and puncture-endpoint exchange

Local copies of the (file-private) `terminalExchange` branch tables; they
are definitionally equal to the originals, which lets us evaluate the
exchange at the two puncture endpoints and prove the global involution. -/

private def exchange0' {m : Nat} (z : TerminalQ m) : TerminalQ m :=
  if z.1 = 2 then
    (if z.2 = 3 then (2, 1) else if z.2 = 1 then (2, 3) else z)
  else if z.2 = 2 then (z.1, 4 - z.1)
  else if z.2 = 4 - z.1 then (z.1, 2)
  else z

private def exchange1' {m : Nat} (z : TerminalQ m) : TerminalQ m :=
  if z.2 = 3 then
    (if z.1 = 0 then (2, 3) else if z.1 = 2 then (0, 3) else z)
  else if z.1 = 1 then (4 - z.2, z.2)
  else if z.1 = 4 - z.2 then (1, z.2)
  else z

private def exchange2' {m : Nat} (z : TerminalQ m) : TerminalQ m :=
  if z.1 + z.2 = 3 then
    (if z = ((2 : ZMod m), (1 : ZMod m)) then (0, 3)
     else if z = ((0 : ZMod m), (3 : ZMod m)) then (2, 1) else z)
  else if z.1 = 1 then (z.1 + z.2 - 2, 2)
  else if z.2 = 2 then (1, z.1 + z.2 - 1)
  else z

private theorem exch0_Ep {m : Nat} [NeZero m] :
    terminalExchange (m := m) 0
        (((2 : ZMod m), (3 : ZMod m)) : TerminalQ m) =
      (((2 : ZMod m), (1 : ZMod m)) : TerminalQ m) := by
  change exchange0' (((2 : ZMod m), (3 : ZMod m)) : TerminalQ m) = _
  simp only [exchange0', if_true]

private theorem exch0_Em {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    terminalExchange (m := m) 0
        (((2 : ZMod m), (1 : ZMod m)) : TerminalQ m) =
      (((2 : ZMod m), (3 : ZMod m)) : TerminalQ m) := by
  change exchange0' (((2 : ZMod m), (1 : ZMod m)) : TerminalQ m) = _
  simp only [exchange0', if_true]
  rw [if_neg (zNe13 hm)]

private theorem exch1_Ep {m : Nat} [NeZero m] :
    terminalExchange (m := m) 1
        (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m) =
      (((2 : ZMod m), (3 : ZMod m)) : TerminalQ m) := by
  change exchange1' (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m) = _
  simp only [exchange1', if_true]

private theorem exch1_Em {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    terminalExchange (m := m) 1
        (((2 : ZMod m), (3 : ZMod m)) : TerminalQ m) =
      (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m) := by
  change exchange1' (((2 : ZMod m), (3 : ZMod m)) : TerminalQ m) = _
  simp only [exchange1', if_true]
  rw [if_neg ((zNe02 hm).symm)]

private theorem exch2_Ep {m : Nat} [NeZero m] :
    terminalExchange (m := m) 2
        (((2 : ZMod m), (1 : ZMod m)) : TerminalQ m) =
      (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m) := by
  change exchange2' (((2 : ZMod m), (1 : ZMod m)) : TerminalQ m) = _
  simp only [exchange2', if_true]
  rw [if_pos (show (2 : ZMod m) + 1 = 3 by norm_num)]

private theorem exch2_Em {m : Nat} [NeZero m] (hm : 6 ≤ m) :
    terminalExchange (m := m) 2
        (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m) =
      (((2 : ZMod m), (1 : ZMod m)) : TerminalQ m) := by
  change exchange2' (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m) = _
  simp only [exchange2', if_true]
  rw [if_pos (show (0 : ZMod m) + 3 = 3 by norm_num),
    if_neg (pair_ne_left (zNe02 hm))]

private theorem invol0 {m : Nat} [NeZero m] (hm : 6 ≤ m)
    (z : TerminalQ m) :
    terminalExchange (m := m) 0 (terminalExchange (m := m) 0 z) = z := by
  by_cases hA : z.2 = 2
  · have hz : z = terminalEndpointA (m := m) 0 z.1 := Prod.ext rfl hA
    rw [hz, terminalExchange_endpointA hm 0 z.1,
      terminalExchange_endpointB hm 0 z.1]
  · by_cases hB : z.2 = 4 - z.1
    · have hz : z = terminalEndpointB (m := m) 0 z.1 := Prod.ext rfl hB
      rw [hz, terminalExchange_endpointB hm 0 z.1,
        terminalExchange_endpointA hm 0 z.1]
    · by_cases h1 : z.1 = 2
      · by_cases h3 : z.2 = 3
        · have hz : z = (((2 : ZMod m), (3 : ZMod m)) : TerminalQ m) :=
            Prod.ext h1 h3
          rw [hz, exch0_Ep, exch0_Em hm]
        · by_cases hOne : z.2 = 1
          · have hz : z = (((2 : ZMod m), (1 : ZMod m)) : TerminalQ m) :=
              Prod.ext h1 hOne
            rw [hz, exch0_Em hm, exch0_Ep]
          · have hfix : terminalExchange (m := m) 0 z = z := by
              change exchange0' z = z
              simp only [exchange0']
              rw [if_pos h1, if_neg h3, if_neg hOne]
            rw [hfix, hfix]
      · have hfix : terminalExchange (m := m) 0 z = z := by
          change exchange0' z = z
          simp only [exchange0']
          rw [if_neg h1, if_neg hA, if_neg hB]
        rw [hfix, hfix]

private theorem invol1 {m : Nat} [NeZero m] (hm : 6 ≤ m)
    (z : TerminalQ m) :
    terminalExchange (m := m) 1 (terminalExchange (m := m) 1 z) = z := by
  by_cases hA : z.1 = 1
  · have hz : z = terminalEndpointA (m := m) 1 z.2 := Prod.ext hA rfl
    rw [hz, terminalExchange_endpointA hm 1 z.2,
      terminalExchange_endpointB hm 1 z.2]
  · by_cases hB : z.1 = 4 - z.2
    · have hz : z = terminalEndpointB (m := m) 1 z.2 := Prod.ext hB rfl
      rw [hz, terminalExchange_endpointB hm 1 z.2,
        terminalExchange_endpointA hm 1 z.2]
    · by_cases h3 : z.2 = 3
      · by_cases h0 : z.1 = 0
        · have hz : z = (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m) :=
            Prod.ext h0 h3
          rw [hz, exch1_Ep, exch1_Em hm]
        · by_cases h2 : z.1 = 2
          · have hz : z = (((2 : ZMod m), (3 : ZMod m)) : TerminalQ m) :=
              Prod.ext h2 h3
            rw [hz, exch1_Em hm, exch1_Ep]
          · have hfix : terminalExchange (m := m) 1 z = z := by
              change exchange1' z = z
              simp only [exchange1']
              rw [if_pos h3, if_neg h0, if_neg h2]
            rw [hfix, hfix]
      · have hfix : terminalExchange (m := m) 1 z = z := by
          change exchange1' z = z
          simp only [exchange1']
          rw [if_neg h3, if_neg hA, if_neg hB]
        rw [hfix, hfix]

private theorem invol2 {m : Nat} [NeZero m] (hm : 6 ≤ m)
    (z : TerminalQ m) :
    terminalExchange (m := m) 2 (terminalExchange (m := m) 2 z) = z := by
  by_cases hA : z.1 = 1
  · have hz : z = terminalEndpointA (m := m) 2 (z.2 + 1) := by
      refine Prod.ext hA ?_
      change z.2 = z.2 + 1 - 1
      ring
    rw [hz, terminalExchange_endpointA hm 2 (z.2 + 1),
      terminalExchange_endpointB hm 2 (z.2 + 1)]
  · by_cases hB : z.2 = 2
    · have hz : z = terminalEndpointB (m := m) 2 (z.1 + 2) := by
        refine Prod.ext ?_ hB
        change z.1 = z.1 + 2 - 2
        ring
      rw [hz, terminalExchange_endpointB hm 2 (z.1 + 2),
        terminalExchange_endpointA hm 2 (z.1 + 2)]
    · by_cases hsum : z.1 + z.2 = 3
      · by_cases hEp : z = (((2 : ZMod m), (1 : ZMod m)) : TerminalQ m)
        · rw [hEp, exch2_Ep, exch2_Em hm]
        · by_cases hEm : z = (((0 : ZMod m), (3 : ZMod m)) : TerminalQ m)
          · rw [hEm, exch2_Em hm, exch2_Ep]
          · have hfix : terminalExchange (m := m) 2 z = z := by
              change exchange2' z = z
              simp only [exchange2']
              rw [if_pos hsum, if_neg hEp, if_neg hEm]
            rw [hfix, hfix]
      · have hfix : terminalExchange (m := m) 2 z = z := by
          change exchange2' z = z
          simp only [exchange2']
          rw [if_neg hsum, if_neg hA, if_neg hB]
        rw [hfix, hfix]

/-- The paper endpoint exchange is a global involution (every color,
every point). -/
private theorem terminalExchange_invol {m : Nat} [NeZero m] (hm : 6 ≤ m)
    (c : TorusColor 3) (z : TerminalQ m) :
    terminalExchange c (terminalExchange c z) = z := by
  fin_cases c
  · exact invol0 hm z
  · exact invol1 hm z
  · exact invol2 hm z

private theorem exchange_endpointEplus {m : Nat} [NeZero m] (_hm : 6 ≤ m)
    (c : TorusColor 3) :
    terminalExchange c (terminalEndpointEplus (m := m) c) =
      terminalEndpointEminus (m := m) c := by
  fin_cases c
  · exact exch0_Ep
  · exact exch1_Ep
  · exact exch2_Ep

private theorem exchange_endpointEminus {m : Nat} [NeZero m] (hm : 6 ≤ m)
    (c : TorusColor 3) :
    terminalExchange c (terminalEndpointEminus (m := m) c) =
      terminalEndpointEplus (m := m) c := by
  fin_cases c
  · exact exch0_Em hm
  · exact exch1_Em hm
  · exact exch2_Em hm

/-! ## Interval data: heads, lengths, per-fiber pairing -/

/-- Head of the interval ending at the rank point `n`: the exchange
partner of `endpointPoint m c n` on the same fiber. -/
private def headAt {m : Nat} [NeZero m] (c : TorusColor 3)
    (n : EndpointLabel m) : TerminalQ m :=
  terminalExchange c (endpointPoint m c n)

/-- Length of the straight interval from `headAt c n` to the rank point
`endpointPoint m c n` along the fiber direction `Δ_c`. -/
private def lenAt {m : Nat} [NeZero m] (c : TorusColor 3)
    (n : EndpointLabel m) : ℕ :=
  (phi c (endpointPoint m c n) - phi c (headAt c n)).val

/-- The pair structure at a rank point: the exchange partner lies on the
same fiber, is distinct, and the two points are exactly the active points
of that fiber. -/
private theorem pair_spec {m : Nat} [NeZero m] (hm : 6 ≤ m)
    (c : TorusColor 3) (n : EndpointLabel m) :
    terminalFiberLabel c (headAt c n) =
        terminalFiberLabel c (endpointPoint m c n) ∧
      headAt c n ≠ endpointPoint m c n ∧
      ∀ z : TerminalQ m,
        (activePred c z ∧
            terminalFiberLabel c z =
              terminalFiberLabel c (endpointPoint m c n)) ↔
          (z = endpointPoint m c n ∨ z = headAt c n) := by
  have hvalid := endpointDesc_valid_of_label hm c n
  have hpt := endpointPoint_eq_descPoint c n
  cases hd : endpointDesc m c n with
  | A r =>
      rw [hd] at hvalid hpt
      have hr : r ≠ endpointCollisionIndex (m := m) c := hvalid
      have hptA : endpointPoint m c n = terminalEndpointA (m := m) c r :=
        hpt
      have hhead : headAt c n = terminalEndpointB (m := m) c r := by
        change terminalExchange c (endpointPoint m c n) = _
        rw [hptA]
        exact terminalExchange_endpointA hm c r
      refine ⟨?_, ?_, ?_⟩
      · rw [hhead, hptA, terminalFiberLabel_endpointB,
          terminalFiberLabel_endpointA]
      · rw [hhead, hptA]
        exact (endpointA_ne_endpointB_of_ne_collision c hr).symm
      · intro z
        rw [hhead, hptA, terminalFiberLabel_endpointA]
        exact active_iff_pair_on_generic_fiber hm c hr z
  | B r =>
      rw [hd] at hvalid hpt
      have hr : r ≠ endpointCollisionIndex (m := m) c := hvalid
      have hptB : endpointPoint m c n = terminalEndpointB (m := m) c r :=
        hpt
      have hhead : headAt c n = terminalEndpointA (m := m) c r := by
        change terminalExchange c (endpointPoint m c n) = _
        rw [hptB]
        exact terminalExchange_endpointB hm c r
      refine ⟨?_, ?_, ?_⟩
      · rw [hhead, hptB, terminalFiberLabel_endpointA,
          terminalFiberLabel_endpointB]
      · rw [hhead, hptB]
        exact endpointA_ne_endpointB_of_ne_collision c hr
      · intro z
        rw [hhead, hptB, terminalFiberLabel_endpointB]
        exact (active_iff_pair_on_generic_fiber hm c hr z).trans or_comm
  | Eplus =>
      rw [hd] at hpt
      have hptE : endpointPoint m c n =
          terminalEndpointEplus (m := m) c := hpt
      have hhead : headAt c n = terminalEndpointEminus (m := m) c := by
        change terminalExchange c (endpointPoint m c n) = _
        rw [hptE]
        exact exchange_endpointEplus hm c
      refine ⟨?_, ?_, ?_⟩
      · rw [hhead, hptE, terminalFiberLabel_endpointEminus,
          terminalFiberLabel_endpointEplus]
      · rw [hhead, hptE]
        exact (endpointEplus_ne_endpointEminus hm c).symm
      · intro z
        rw [hhead, hptE, terminalFiberLabel_endpointEplus]
        exact active_iff_pair_on_collision_fiber hm c z
  | Eminus =>
      rw [hd] at hpt
      have hptE : endpointPoint m c n =
          terminalEndpointEminus (m := m) c := hpt
      have hhead : headAt c n = terminalEndpointEplus (m := m) c := by
        change terminalExchange c (endpointPoint m c n) = _
        rw [hptE]
        exact exchange_endpointEminus hm c
      refine ⟨?_, ?_, ?_⟩
      · rw [hhead, hptE, terminalFiberLabel_endpointEplus,
          terminalFiberLabel_endpointEminus]
      · rw [hhead, hptE]
        exact endpointEplus_ne_endpointEminus hm c
      · intro z
        rw [hhead, hptE, terminalFiberLabel_endpointEminus]
        exact (active_iff_pair_on_collision_fiber hm c z).trans or_comm

private theorem lenAt_pos {m : Nat} [NeZero m] (hm : 6 ≤ m)
    (c : TorusColor 3) (n : EndpointLabel m) : 0 < lenAt c n := by
  obtain ⟨hfib, hne, -⟩ := pair_spec hm c n
  refine Nat.pos_of_ne_zero fun h0 => hne ?_
  have hx : phi c (endpointPoint m c n) - phi c (headAt c n) = 0 :=
    (ZMod.val_eq_zero _).mp h0
  have hphi : phi c (headAt c n) = phi c (endpointPoint m c n) :=
    (sub_eq_zero.mp hx).symm
  exact point_eq_of_fiber_phi c hfib hphi

/-! ## η on the rank list, via the recurrence rank step -/

private theorem rec_exchange_eq (m : Nat) [NeZero m] (hm : 6 ≤ m) :
    (terminalA2EndpointRecurrence m hm).exchange =
      terminalExchange (m := m) := rfl

/-- The paper jump `η_c` carries the rank point `n` to the head of the
next interval. -/
private theorem eta_pt {m : Nat} [NeZero m] (hmEven : Even m) (hm : 6 ≤ m)
    (c : TorusColor 3) (n : EndpointLabel m) :
    terminalEta (m := m) c (endpointPoint m c n) =
      headAt c (endpointRankSucc m n) := by
  have hstep := compressedEndpoint_rank_step_of_desc_rank_step hm
    (terminalA2EndpointRecurrence m hm) c
    (endpointDesc_rank_step hmEven hm c) n
  simp only [D3TerminalA2Parametric.terminalCompressedEndpointReturn]
    at hstep
  rw [rec_exchange_eq m hm] at hstep
  have h2 := congrArg (terminalExchange (m := m) c) hstep
  rw [terminalExchange_invol hm c] at h2
  exact h2

/-! ## Interval walk and traversal -/

/-- Inside an interval, the collapsed return is the straight fiber step:
each intermediate point is inactive, so `η_c` is the identity there. -/
private theorem walk {m : Nat} [NeZero m] (hm : 6 ≤ m) (c : TorusColor 3)
    (n : EndpointLabel m) :
    ∀ j : ℕ, j < lenAt c n →
      (terminalReturn (m := m) c)^[j] (headAt c n) =
        headAt c n + j • terminalDelta (m := m) c := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
      intro hstep_lt
      have hj : j < lenAt c n := Nat.lt_of_succ_lt hstep_lt
      have hmlt : lenAt c n < m := ZMod.val_lt _
      have hm0 : 0 < m := by omega
      rw [Function.iterate_succ_apply', ih hj]
      change terminalEta (m := m) c
          (headAt c n + j • terminalDelta (m := m) c +
            terminalDelta (m := m) c) =
        headAt c n + (j + 1) • terminalDelta (m := m) c
      have hsum : headAt c n + j • terminalDelta (m := m) c +
          terminalDelta (m := m) c =
          headAt c n + (j + 1) • terminalDelta (m := m) c := by
        rw [succ_nsmul, ← add_assoc]
      have hnot : ¬ activePred c
          (headAt c n + (j + 1) • terminalDelta (m := m) c) := by
        intro hact
        obtain ⟨hfib, -, hpair⟩ := pair_spec hm c n
        have hfw : terminalFiberLabel c
            (headAt c n + (j + 1) • terminalDelta (m := m) c) =
            terminalFiberLabel c (endpointPoint m c n) := by
          rw [fiber_add_nsmul, hfib]
        rcases (hpair _).mp ⟨hact, hfw⟩ with hwp | hwh
        · have hphi := congrArg (phi c) hwp
          rw [phi_add_nsmul] at hphi
          have hlen : ((lenAt c n : ℕ) : ZMod m) =
              phi c (endpointPoint m c n) - phi c (headAt c n) :=
            ZMod.natCast_zmod_val _
          have hj1 : (((j + 1 : ℕ)) : ZMod m) =
              ((lenAt c n : ℕ) : ZMod m) := by
            rw [hlen]
            linear_combination hphi
          have := natCast_inj_of_lt (by omega) (by omega) hj1
          omega
        · have hphi := congrArg (phi c) hwh
          rw [phi_add_nsmul] at hphi
          have hj1 : (((j + 1 : ℕ)) : ZMod m) = ((0 : ℕ) : ZMod m) := by
            rw [Nat.cast_zero]
            linear_combination hphi
          have := natCast_inj_of_lt (by omega) (by omega) hj1
          omega
      rw [hsum]
      exact terminalEta_eq_self_of_not_active hm c _ hnot

/-- Full traversal of one interval: `len` straight steps followed by the
final `η_c` jump land on the head of the next interval. -/
private theorem traverse {m : Nat} [NeZero m] (hmEven : Even m)
    (hm : 6 ≤ m) (c : TorusColor 3) (n : EndpointLabel m) :
    (terminalReturn (m := m) c)^[lenAt c n] (headAt c n) =
      headAt c (endpointRankSucc m n) := by
  have hpos := lenAt_pos hm c n
  have hfib : terminalFiberLabel c (endpointPoint m c n) =
      terminalFiberLabel c (headAt c n) := (pair_spec hm c n).1.symm
  obtain ⟨i, hi⟩ : ∃ i, lenAt c n = i + 1 := ⟨lenAt c n - 1, by omega⟩
  have htarget : headAt c n + (i + 1) • terminalDelta (m := m) c =
      endpointPoint m c n := by
    rw [← hi]
    exact add_val_smul_delta c hfib
  rw [hi, Function.iterate_succ_apply', walk hm c n i (by omega)]
  change terminalEta (m := m) c
      (headAt c n + i • terminalDelta (m := m) c +
        terminalDelta (m := m) c) = headAt c (endpointRankSucc m n)
  rw [add_assoc, ← succ_nsmul, htarget]
  exact eta_pt hmEven hm c n

/-! ## The rank list reaches every active point (cardinality argument) -/

private def descEquiv (m : Nat) :
    EndpointDesc m ≃ (ZMod m ⊕ ZMod m) ⊕ Bool where
  toFun d :=
    match d with
    | .A r => Sum.inl (Sum.inl r)
    | .B r => Sum.inl (Sum.inr r)
    | .Eplus => Sum.inr true
    | .Eminus => Sum.inr false
  invFun x :=
    match x with
    | Sum.inl (Sum.inl r) => .A r
    | Sum.inl (Sum.inr r) => .B r
    | Sum.inr true => .Eplus
    | Sum.inr false => .Eminus
  left_inv d := by cases d <;> rfl
  right_inv x := by
    rcases x with (r | r) | b
    · rfl
    · rfl
    · cases b <;> rfl

private instance instFiniteEndpointDesc (m : Nat) [NeZero m] :
    Finite (EndpointDesc m) :=
  Finite.of_equiv _ (descEquiv m).symm

private theorem card_endpointDesc (m : Nat) [NeZero m] :
    Nat.card (EndpointDesc m) = 2 * m + 2 := by
  have hb : Nat.card Bool = 2 := by
    simp [Nat.card_eq_fintype_card]
  rw [Nat.card_congr (descEquiv m), Nat.card_sum, Nat.card_sum,
    Nat.card_zmod, hb]
  omega

/-- Every valid descriptor occurs in the closed-form rank list: the list
is injective into the `2m` valid descriptors, and there are exactly `2m`
of them. -/
private theorem exists_label_of_valid {m : Nat} [NeZero m]
    (hmEven : Even m) (hm : 6 ≤ m) (c : TorusColor 3)
    {d : EndpointDesc m} (hd : endpointDescValid (m := m) c d) :
    ∃ n : EndpointLabel m, endpointDesc m c n = d := by
  have hsub : Set.range (endpointDesc m c) ⊆
      {e : EndpointDesc m | endpointDescValid (m := m) c e} := by
    rintro e ⟨n, rfl⟩
    exact endpointDesc_valid_of_label hm c n
  have hcompl :
      {e : EndpointDesc m | endpointDescValid (m := m) c e}ᶜ =
        {EndpointDesc.A (endpointCollisionIndex (m := m) c),
          EndpointDesc.B (endpointCollisionIndex (m := m) c)} := by
    ext e
    cases e with
    | A r => simp [endpointDescValid]
    | B r => simp [endpointDescValid]
    | Eplus => simp [endpointDescValid]
    | Eminus => simp [endpointDescValid]
  have hccard :
      ({e : EndpointDesc m | endpointDescValid (m := m) c e}ᶜ).ncard
        = 2 := by
    rw [hcompl]
    exact Set.ncard_pair (by simp)
  have hVcard :
      ({e : EndpointDesc m |
        endpointDescValid (m := m) c e}).ncard = 2 * m := by
    have h := Set.ncard_add_ncard_compl
      {e : EndpointDesc m | endpointDescValid (m := m) c e}
    rw [hccard, card_endpointDesc m] at h
    omega
  have hrcard : (Set.range (endpointDesc m c)).ncard = 2 * m := by
    rw [Set.ncard_range_of_injective
      (endpointDesc_injective_of_even_six_le hmEven hm c)]
    simp [Nat.card_eq_fintype_card]
  have heq := Set.eq_of_subset_of_ncard_le hsub
    (le_of_eq (hVcard.trans hrcard.symm))
  have hmem : d ∈ Set.range (endpointDesc m c) := by
    rw [heq]
    exact hd
  exact hmem

/-- Every active point of color `c` is a rank point of the closed-form
endpoint list. -/
private theorem mem_range_pt_of_active {m : Nat} [NeZero m]
    (hmEven : Even m) (hm : 6 ≤ m) (c : TorusColor 3) {z : TerminalQ m}
    (hz : activePred c z) :
    ∃ n : EndpointLabel m, endpointPoint m c n = z := by
  rcases (activePred_iff_endpoint hm c z).mp hz with
    ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | rfl | rfl
  · obtain ⟨n, hn⟩ := exists_label_of_valid hmEven hm c
      (d := EndpointDesc.A r) hr
    exact ⟨n, by rw [endpointPoint_eq_descPoint, hn]; rfl⟩
  · obtain ⟨n, hn⟩ := exists_label_of_valid hmEven hm c
      (d := EndpointDesc.B r) hr
    exact ⟨n, by rw [endpointPoint_eq_descPoint, hn]; rfl⟩
  · obtain ⟨n, hn⟩ := exists_label_of_valid hmEven hm c
      (d := EndpointDesc.Eplus) trivial
    exact ⟨n, by rw [endpointPoint_eq_descPoint, hn]; rfl⟩
  · obtain ⟨n, hn⟩ := exists_label_of_valid hmEven hm c
      (d := EndpointDesc.Eminus) trivial
    exact ⟨n, by rw [endpointPoint_eq_descPoint, hn]; rfl⟩

/-! ## Coverage -/

/-- Every point of `Q_m` is interior to one of the two complementary
intervals of its fiber. -/
private theorem cover {m : Nat} [NeZero m] (hmEven : Even m) (hm : 6 ≤ m)
    (c : TorusColor 3) (z : TerminalQ m) :
    ∃ k : EndpointLabel m, ∃ j : ℕ,
      j < lenAt c (endpointRankSucc m k) ∧
        (terminalReturn (m := m) c)^[j]
          (headAt c (endpointRankSucc m k)) = z := by
  obtain ⟨y, hyA, hyF⟩ :
      ∃ y : TerminalQ m, activePred c y ∧
        terminalFiberLabel c y = terminalFiberLabel c z := by
    by_cases hg : terminalFiberLabel c z =
        endpointCollisionIndex (m := m) c
    · refine ⟨terminalEndpointEplus (m := m) c, ?_⟩
      have h := (active_iff_pair_on_collision_fiber hm c
        (terminalEndpointEplus (m := m) c)).mpr (Or.inl rfl)
      exact ⟨h.1, h.2.trans hg.symm⟩
    · refine ⟨terminalEndpointA (m := m) c (terminalFiberLabel c z), ?_⟩
      have h := (active_iff_pair_on_generic_fiber hm c hg
        (terminalEndpointA (m := m) c (terminalFiberLabel c z))).mpr
        (Or.inl rfl)
      exact ⟨h.1, h.2⟩
  obtain ⟨n₀, hn₀⟩ := mem_range_pt_of_active hmEven hm c hyA
  obtain ⟨hfib₀, -, hpair₀⟩ := pair_spec hm c n₀
  have hzfib : terminalFiberLabel c (endpointPoint m c n₀) =
      terminalFiberLabel c z := by
    rw [hn₀]
    exact hyF
  have hfibz₀ : terminalFiberLabel c z =
      terminalFiberLabel c (headAt c n₀) := (hfib₀.trans hzfib).symm
  have hact₁ : activePred c (headAt c n₀) :=
    ((hpair₀ (headAt c n₀)).mpr (Or.inr rfl)).1
  obtain ⟨n₁, hn₁⟩ := mem_range_pt_of_active hmEven hm c hact₁
  have hhead₁ : headAt c n₁ = endpointPoint m c n₀ := by
    change terminalExchange c (endpointPoint m c n₁) = _
    rw [hn₁]
    exact terminalExchange_invol hm c (endpointPoint m c n₀)
  obtain ⟨k₀, hk₀⟩ :=
    (endpointRankSucc_singleCycle (m := m)).1.2 n₀
  obtain ⟨k₁, hk₁⟩ :=
    (endpointRankSucc_singleCycle (m := m)).1.2 n₁
  by_cases ht : (phi c z - phi c (headAt c n₀)).val < lenAt c n₀
  · refine ⟨k₀, (phi c z - phi c (headAt c n₀)).val, ?_, ?_⟩
    · rw [hk₀]
      exact ht
    · rw [hk₀, walk hm c n₀ _ ht]
      exact add_val_smul_delta c hfibz₀
  · have hle : lenAt c n₀ ≤ (phi c z - phi c (headAt c n₀)).val :=
      Nat.le_of_not_lt ht
    have htm : (phi c z - phi c (headAt c n₀)).val < m := ZMod.val_lt _
    have hx0 : phi c (endpointPoint m c n₀) - phi c (headAt c n₀) ≠ 0 := by
      intro h0
      have hpos := lenAt_pos hm c n₀
      have h0' : lenAt c n₀ = 0 := by
        change (phi c (endpointPoint m c n₀) - phi c (headAt c n₀)).val = 0
        rw [h0, ZMod.val_zero]
      omega
    have hL1 : lenAt c n₁ = m - lenAt c n₀ := by
      change (phi c (endpointPoint m c n₁) - phi c (headAt c n₁)).val = _
      rw [hn₁, hhead₁,
        show phi c (headAt c n₀) - phi c (endpointPoint m c n₀) =
            -(phi c (endpointPoint m c n₀) - phi c (headAt c n₀)) by ring,
        ZMod.neg_val, if_neg hx0]
      rfl
    have hcast : phi c z - phi c (headAt c n₁) =
        (((phi c z - phi c (headAt c n₀)).val - lenAt c n₀ : ℕ) :
          ZMod m) := by
      rw [hhead₁, Nat.cast_sub hle, ZMod.natCast_zmod_val,
        show ((lenAt c n₀ : ℕ) : ZMod m) =
            phi c (endpointPoint m c n₀) - phi c (headAt c n₀) from
          ZMod.natCast_zmod_val _]
      ring
    have ht' : (phi c z - phi c (headAt c n₁)).val =
        (phi c z - phi c (headAt c n₀)).val - lenAt c n₀ := by
      rw [hcast, ZMod.val_natCast_of_lt (by omega)]
    have hbound : (phi c z - phi c (headAt c n₁)).val < lenAt c n₁ := by
      rw [ht', hL1]
      omega
    refine ⟨k₁, (phi c z - phi c (headAt c n₁)).val, ?_, ?_⟩
    · rw [hk₁]
      exact hbound
    · rw [hk₁, walk hm c n₁ _ hbound]
      have hfibz₁ : terminalFiberLabel c z =
          terminalFiberLabel c (headAt c n₁) := by
        rw [hhead₁]
        exact hzfib.symm
      exact add_val_smul_delta c hfibz₁

/-! ## H1a per-color cyclicity and the family -/

/-- H1a carrier cyclicity (paper `lem:terminal-cyclicity`, generic case):
for every even `m ≥ 6` and every terminal color, the collapsed terminal
carrier `terminalReturn c` is a single `m²`-cycle on `Q_m`. -/
theorem terminalReturn_singleCycle_of_even_six_le {m : Nat} [NeZero m]
    (hmEven : Even m) (hm : 6 ≤ m) (c : TorusColor 3) :
    Shared.IsSingleCycleMap (TerminalA2LowMod.terminalReturn (m := m) c) :=
  single_cycle_of_interval_splice
    (TerminalA2LowMod.terminalReturn (m := m) c)
    (endpointRankSucc m)
    (fun k => headAt c (endpointRankSucc m k))
    (fun k => lenAt c (endpointRankSucc m k))
    (fun k => lenAt_pos hm c (endpointRankSucc m k))
    (fun k => traverse hmEven hm c (endpointRankSucc m k))
    endpointRankSucc_singleCycle
    (cover hmEven hm c)

/-- H1a, assembled: terminal-carrier cyclicity for the whole even range.
`m = 4` is the finite orbit certificate `terminalA2M4FiniteCyclicity`;
every even `m ≥ 6` is the interval-splice theorem above. -/
theorem terminalA2CarrierCyclicityFamily :
    D3TerminalA2Parametric.TerminalA2CarrierCyclicityFamily := by
  intro m hm c
  letI := RootFlatCycle.neZero_of_evenModulusRange hm
  have hmEven : Even m := by
    rcases hm.2 with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  by_cases h4 : m = 4
  · subst h4
    simpa [D3TerminalA2Parametric.terminalReturnOfRange] using
      D3TerminalA2Parametric.terminalA2M4FiniteCyclicity.terminalReturn_singleCycle
        c
  · have h6 : 6 ≤ m := by
      have h4le : 4 ≤ m := hm.1
      rcases hm.2 with ⟨k, hk⟩
      omega
    simpa [D3TerminalA2Parametric.terminalReturnOfRange] using
      terminalReturn_singleCycle_of_even_six_le hmEven h6 c

end TerminalA2IntervalSplice
end V28Hard
end EvenV11
