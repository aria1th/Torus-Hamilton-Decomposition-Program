import EvenV11.V28Hard.D3EvenRailSeam
import EvenV11.V28Hard.EndpointRowSchedule

/-!
# D3-even rail seam: the schedule and the return-map reduction (module 2)

This file installs the rail-seam wild layer of
`EvenV11.V28Hard.D3EvenRailSeam` into a full standard-lift root-flat schedule
(`docs/WILDE_SEARCH_20260610.md` §3.2, §4 items 2-3; numeric ground truth:
`scripts/search_d3_even_dir.py construct`).

The schedule (`railDir`) has `m − 1` constant cheap layers built from the
three translations `id : c ↦ c`, `ρ⁺ : c ↦ c+1`, `ρ⁺⁺ : c ↦ c+2`, with the
script's exact layer assignment:

* `3 ∤ m`: layer `0` is `ρ⁺`, layers `1 .. m−2` are `ρ⁺⁺`;
* `3 ∣ m`: layers `0 .. m−6` are `id`, layer `m−5` is `ρ⁺`, layers
  `m−4 .. m−2` are `ρ⁺⁺`;

and the wild layer `wildRowRoot` at `t = m − 1` in both cases.

Proved here:

* **RF1** (`railSchedule_rowLatin`): free, every row is a permutation;
* **RF2** (`railSchedule_layerBijective`): cheap layers are translations,
  the wild layer map is `w ↦ rhoRoot c w + e_c` and `rhoRoot` is bijective
  (module 1);
* **cheap collapse**: the composition of the `m − 1` cheap layers is the
  translation by `cheapVec m c` (`railReturn_apply`), so the color return
  map is `R_c = (T_{e_c} ∘ ρ_c) ∘ T_{v_c}`;
* **conjugated drift**: `e_c + v_c = u_c` is the explicit `driftPair m c`
  (`stepVec_add_cheapVec`), in pair coordinates

  | case | `u₀` | `u₁` | `u₂` |
  |---|---|---|---|
  | `3 ∤ m` | `(1, 1)` | `(m−2, 1)` | `(1, m−2)` |
  | `3 ∣ m` | `(m−4, 1)` | `(3, m−4)` | `(1, 3)` |

* **the module-3 handoff** (`railReturn_singleCycle_of_core`): if
  `w ↦ rhoRoot c w + driftVec m c` is a single `m²`-cycle then so is the
  schedule return `railReturn m c` (translation conjugacy), and the final
  packaging stub `railCycleData` assembling `RootFlatCycleData 2 m` from the
  three per-color core cyclicity inputs.

No RF3 claim is made here — module 3 owns the three core statements.

Decide anchors at `m ∈ {4, 6}` (plus drift tables at `m ∈ {8, 12}`) pin the
layer assignment, the drift constants and sample return values against the
script's output.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace EvenV11
namespace V28Hard
namespace D3EvenRailSchedule

open Shared
open TerminalA2LowMod
open D3TerminalA2Parametric
open D3EvenRailSeam
open EndpointRowSchedule

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## The cheap rows and the layer table -/

section RowTable

/-- The cheap translation row `ρ⁺ : c ↦ c + 1`. -/
def rotPlus : Equiv.Perm (Fin 3) where
  toFun c := c + 1
  invFun c := c - 1
  left_inv c := by fin_cases c <;> rfl
  right_inv c := by fin_cases c <;> rfl

/-- The cheap translation row `ρ⁺⁺ : c ↦ c + 2`. -/
def rotPlusPlus : Equiv.Perm (Fin 3) where
  toFun c := c + 2
  invFun c := c - 2
  left_inv c := by fin_cases c <;> rfl
  right_inv c := by fin_cases c <;> rfl

/-- The cheap row at (Nat) layer index `t`, exactly as assigned by
`scripts/search_d3_even_dir.py construct`: for `3 ∤ m` one `ρ⁺` (layer 0)
then `ρ⁺⁺`; for `3 ∣ m` the multiset `(m−5)×id, 1×ρ⁺, 3×ρ⁺⁺` in that order.
Only indices `t ≤ m − 2` are consumed by the schedule. -/
def cheapRowNat (m t : Nat) : Equiv.Perm (Fin 3) :=
  if m % 3 = 0 then
    if t < m - 5 then 1 else if t = m - 5 then rotPlus else rotPlusPlus
  else
    if t = 0 then rotPlus else rotPlusPlus

theorem cheapRowNat_ne_zero {m : Nat} (h3 : m % 3 ≠ 0) :
    cheapRowNat m 0 = rotPlus := by
  unfold cheapRowNat
  rw [if_neg h3, if_pos rfl]

theorem cheapRowNat_ne_succ {m : Nat} (h3 : m % 3 ≠ 0) (k : Nat) :
    cheapRowNat m (k + 1) = rotPlusPlus := by
  unfold cheapRowNat
  rw [if_neg h3, if_neg (Nat.succ_ne_zero k)]

theorem cheapRowNat_dvd_lt {m : Nat} (h3 : m % 3 = 0) {t : Nat}
    (ht : t < m - 5) : cheapRowNat m t = 1 := by
  unfold cheapRowNat
  rw [if_pos h3, if_pos ht]

theorem cheapRowNat_dvd_eq {m : Nat} (h3 : m % 3 = 0) :
    cheapRowNat m (m - 5) = rotPlus := by
  unfold cheapRowNat
  rw [if_pos h3, if_neg (lt_irrefl _), if_pos rfl]

theorem cheapRowNat_dvd_gt {m : Nat} (h3 : m % 3 = 0) {t : Nat}
    (ht : m - 5 < t) : cheapRowNat m t = rotPlusPlus := by
  unfold cheapRowNat
  rw [if_pos h3, if_neg (by omega), if_neg (by omega)]

/-- The full rail-seam row table: cheap constant rows on layers
`0 .. m − 2`, the wild row of module 1 at layer `m − 1`. -/
def railRow (m : Nat) [NeZero m] (t : ZMod m) (w : RootState m) :
    Equiv.Perm (Fin 3) :=
  if t.val = m - 1 then wildRowRoot w else cheapRowNat m t.val

theorem railRow_of_wild {m : Nat} [NeZero m] {t : ZMod m}
    (ht : t.val = m - 1) (w : RootState m) :
    railRow m t w = wildRowRoot w := if_pos ht

theorem railRow_of_cheap {m : Nat} [NeZero m] {t : ZMod m}
    (ht : t.val ≠ m - 1) (w : RootState m) :
    railRow m t w = cheapRowNat m t.val := if_neg ht

/-- The schedule `dir` table over the standard D3 lift. -/
def railDir (m : Nat) [NeZero m] :
    ZMod m → RootState m → TorusColor 3 → TorusDirection 3 :=
  fun t w c => railRow m t w c

/-- The rail-seam root-flat schedule. -/
def railSchedule (m : Nat) [NeZero m] :
    RootFlatSchedule (TorusColor 3) (TorusDirection 3) (RootState m) m :=
  RootFlatCycle.schedule (railDir m)

end RowTable

/-! ## RF1 and the layer-map formulas -/

section Layers

variable {m : Nat} [NeZero m]

/-- **RF1**: every layer row of the rail-seam schedule is a permutation. -/
theorem railSchedule_rowLatin (m : Nat) [NeZero m] :
    (railSchedule m).rowLatin :=
  rowSchedule_rowLatin (fun t w => railRow m t w)

/-- The generic layer map: state-dependent translation by the step vector of
the read direction. -/
theorem railSchedule_layerMap_apply (t : ZMod m) (c : TorusColor 3)
    (w : RootState m) :
    (railSchedule m).layerMap t c w = w + stepVec (railRow m t w c) :=
  rowSchedule_layerMap_apply (fun t w => railRow m t w) t c w

/-- `pairRoot` sends `0` to `0`. -/
theorem pairRoot_zero : pairRoot (0 : TerminalQ m) = (0 : RootState m) := by
  funext j
  fin_cases j <;> rfl

/-- `pairRoot` is additive. -/
theorem pairRoot_add (q q' : TerminalQ m) :
    pairRoot (q + q') = pairRoot q + pairRoot q' := by
  funext j
  fin_cases j <;> rfl

/-- `pairRoot` commutes with subtraction. -/
theorem pairRoot_sub (q q' : TerminalQ m) :
    pairRoot (q - q') = pairRoot q - pairRoot q' := by
  funext j
  fin_cases j <;> rfl

/-- The pair direction vectors of module 1 are the root step vectors. -/
theorem pairRoot_eVec (i : Fin 3) :
    pairRoot (eVec i : TerminalQ m) = stepVec i := by
  fin_cases i <;> (funext j; fin_cases j <;> rfl)

/-- The wild deviation against the wild layer map:
`rhoRoot c w + e_c = w + e_{wildRow w c}`. -/
theorem rhoRoot_add_stepVec (c : Fin 3) (w : RootState m) :
    rhoRoot c w + stepVec c = w + stepVec (wildRowRoot w c) := by
  have h : rhoRoot c w = w + (stepVec (wildRowRoot w c) - stepVec c) := by
    change pairRoot (rho c (rootPair w)) = _
    rw [show rho c (rootPair w)
        = rootPair w + (eVec (wildRow (rootPair w) c) - eVec c) from rfl,
      pairRoot_add, pairRoot_rootPair, pairRoot_sub, pairRoot_eVec,
      pairRoot_eVec]
    rfl
  rw [h]
  abel

/-- The wild layer map at `t = m − 1` is `w ↦ rhoRoot c w + e_c`. -/
theorem railSchedule_layerMap_wild {t : ZMod m} (ht : t.val = m - 1)
    (c : TorusColor 3) (w : RootState m) :
    (railSchedule m).layerMap t c w = rhoRoot c w + stepVec c := by
  rw [railSchedule_layerMap_apply, railRow_of_wild ht,
    ← rhoRoot_add_stepVec c w]

/-- **RF2**: every layer map of the rail-seam schedule is bijective.  Cheap
layers are translations; the wild layer is the translation `+ e_c` after the
bijective deviation `rhoRoot c` of module 1. -/
theorem railSchedule_layerBijective (hm : 4 ≤ m) :
    (railSchedule m).layerBijective := by
  intro t c
  by_cases ht : t.val = m - 1
  · have hmap : (railSchedule m).layerMap t c
        = (fun x : RootState m => x + stepVec c) ∘ rhoRoot c := by
      funext w
      simp only [Function.comp_apply]
      exact railSchedule_layerMap_wild ht c w
    rw [hmap]
    exact (Equiv.addRight (stepVec c)).bijective.comp (rhoRoot_bijective hm c)
  · exact layerMap_bijective_of_constant (fun t w => railRow m t w) t c
      (cheapRowNat m t.val) (fun w => railRow_of_cheap ht w)

end Layers

/-! ## Cheap-layer collapse: partial sums of the cheap step vectors -/

section CheapSum

variable {m : Nat}

/-- Partial sum (in pair coordinates) of the cheap step vectors
`e_{σ_t(c)}` over layers `t < k`. -/
def cheapSum (m : Nat) (c : Fin 3) : Nat → TerminalQ m
  | 0 => 0
  | k + 1 => cheapSum m c k + eVec (cheapRowNat m k c)

theorem cheapSum_zero (c : Fin 3) : cheapSum m c 0 = 0 := rfl

theorem cheapSum_succ (c : Fin 3) (k : Nat) :
    cheapSum m c (k + 1) = cheapSum m c k + eVec (cheapRowNat m k c) := rfl

/-! ### Closed forms, case `3 ∤ m` -/

theorem cheapSumA_zero (h3 : m % 3 ≠ 0) :
    ∀ k : Nat, cheapSum m 0 (k + 1) = (((0 : ZMod m), (1 : ZMod m)))
  | 0 => by
      rw [cheapSum_succ, cheapSum_zero, cheapRowNat_ne_zero h3,
        show (eVec (rotPlus 0) : TerminalQ m) = (0, 1) from rfl, zero_add]
  | k + 1 => by
      rw [cheapSum_succ, cheapSumA_zero h3 k, cheapRowNat_ne_succ h3,
        show (eVec (rotPlusPlus 0) : TerminalQ m) = (0, 0) from rfl,
        Prod.mk_add_mk, add_zero, add_zero]

theorem cheapSumA_one (h3 : m % 3 ≠ 0) :
    ∀ k : Nat, cheapSum m 1 (k + 1) = ((((k : Nat) : ZMod m), (0 : ZMod m)))
  | 0 => by
      rw [cheapSum_succ, cheapSum_zero, cheapRowNat_ne_zero h3,
        show (eVec (rotPlus 1) : TerminalQ m) = (0, 0) from rfl,
        Nat.cast_zero, zero_add]
  | k + 1 => by
      rw [cheapSum_succ, cheapSumA_one h3 k, cheapRowNat_ne_succ h3,
        show (eVec (rotPlusPlus 1) : TerminalQ m) = (1, 0) from rfl,
        Prod.mk_add_mk, add_zero, Nat.cast_succ]

theorem cheapSumA_two (h3 : m % 3 ≠ 0) :
    ∀ k : Nat, cheapSum m 2 (k + 1) = (((1 : ZMod m), ((k : Nat) : ZMod m)))
  | 0 => by
      rw [cheapSum_succ, cheapSum_zero, cheapRowNat_ne_zero h3,
        show (eVec (rotPlus 2) : TerminalQ m) = (1, 0) from rfl,
        Nat.cast_zero, zero_add]
  | k + 1 => by
      rw [cheapSum_succ, cheapSumA_two h3 k, cheapRowNat_ne_succ h3,
        show (eVec (rotPlusPlus 2) : TerminalQ m) = (0, 1) from rfl,
        Prod.mk_add_mk, add_zero, Nat.cast_succ]

/-! ### Closed forms, case `3 ∣ m` (three phases: `id`-run, `ρ⁺`, `ρ⁺⁺`-run) -/

theorem cheapSumB_zero_p1 (h3 : m % 3 = 0) :
    ∀ k, k ≤ m - 5 →
      cheapSum m 0 k = ((((k : Nat) : ZMod m), (0 : ZMod m)))
  | 0, _ => by
      rw [cheapSum_zero, Nat.cast_zero]
      rfl
  | k + 1, hk => by
      rw [cheapSum_succ, cheapSumB_zero_p1 h3 k (by omega),
        cheapRowNat_dvd_lt h3 (by omega),
        show (eVec ((1 : Equiv.Perm (Fin 3)) 0) : TerminalQ m) = (1, 0)
          from rfl,
        Prod.mk_add_mk, add_zero, Nat.cast_succ]

theorem cheapSumB_one_p1 (h3 : m % 3 = 0) :
    ∀ k, k ≤ m - 5 →
      cheapSum m 1 k = (((0 : ZMod m), ((k : Nat) : ZMod m)))
  | 0, _ => by
      rw [cheapSum_zero, Nat.cast_zero]
      rfl
  | k + 1, hk => by
      rw [cheapSum_succ, cheapSumB_one_p1 h3 k (by omega),
        cheapRowNat_dvd_lt h3 (by omega),
        show (eVec ((1 : Equiv.Perm (Fin 3)) 1) : TerminalQ m) = (0, 1)
          from rfl,
        Prod.mk_add_mk, add_zero, Nat.cast_succ]

theorem cheapSumB_two_p1 (h3 : m % 3 = 0) :
    ∀ k, k ≤ m - 5 → cheapSum m 2 k = (0 : TerminalQ m)
  | 0, _ => rfl
  | k + 1, hk => by
      rw [cheapSum_succ, cheapSumB_two_p1 h3 k (by omega),
        cheapRowNat_dvd_lt h3 (by omega),
        show (eVec ((1 : Equiv.Perm (Fin 3)) 2) : TerminalQ m) = 0 from rfl,
        add_zero]

theorem cheapSumB_zero_p2 (h3 : m % 3 = 0) (hm : 4 ≤ m) :
    cheapSum m 0 (m - 4) = ((((m - 5 : Nat) : ZMod m), (1 : ZMod m))) := by
  have h45 : m - 4 = m - 5 + 1 := by omega
  rw [h45, cheapSum_succ, cheapSumB_zero_p1 h3 (m - 5) le_rfl,
    cheapRowNat_dvd_eq h3,
    show (eVec (rotPlus 0) : TerminalQ m) = (0, 1) from rfl,
    Prod.mk_add_mk, add_zero, zero_add]

theorem cheapSumB_one_p2 (h3 : m % 3 = 0) (hm : 4 ≤ m) :
    cheapSum m 1 (m - 4) = (((0 : ZMod m), ((m - 5 : Nat) : ZMod m))) := by
  have h45 : m - 4 = m - 5 + 1 := by omega
  rw [h45, cheapSum_succ, cheapSumB_one_p1 h3 (m - 5) le_rfl,
    cheapRowNat_dvd_eq h3,
    show (eVec (rotPlus 1) : TerminalQ m) = (0, 0) from rfl,
    Prod.mk_add_mk, add_zero, add_zero]

theorem cheapSumB_two_p2 (h3 : m % 3 = 0) (hm : 4 ≤ m) :
    cheapSum m 2 (m - 4) = (((1 : ZMod m), (0 : ZMod m))) := by
  have h45 : m - 4 = m - 5 + 1 := by omega
  rw [h45, cheapSum_succ, cheapSumB_two_p1 h3 (m - 5) le_rfl,
    cheapRowNat_dvd_eq h3,
    show (eVec (rotPlus 2) : TerminalQ m) = (1, 0) from rfl, zero_add]

theorem cheapSumB_zero_p3 (h3 : m % 3 = 0) (hm : 4 ≤ m) :
    ∀ j, j ≤ 3 →
      cheapSum m 0 (m - 4 + j)
        = ((((m - 5 : Nat) : ZMod m), (1 : ZMod m)))
  | 0, _ => by
      rw [Nat.add_zero, cheapSumB_zero_p2 h3 hm]
  | j + 1, hj => by
      have hsplit : m - 4 + (j + 1) = (m - 4 + j) + 1 := by omega
      rw [hsplit, cheapSum_succ, cheapSumB_zero_p3 h3 hm j (by omega),
        cheapRowNat_dvd_gt h3 (by omega),
        show (eVec (rotPlusPlus 0) : TerminalQ m) = (0, 0) from rfl,
        Prod.mk_add_mk, add_zero, add_zero]

theorem cheapSumB_one_p3 (h3 : m % 3 = 0) (hm : 4 ≤ m) :
    ∀ j, j ≤ 3 →
      cheapSum m 1 (m - 4 + j)
        = ((((j : Nat) : ZMod m), ((m - 5 : Nat) : ZMod m)))
  | 0, _ => by
      rw [Nat.add_zero, cheapSumB_one_p2 h3 hm, Nat.cast_zero]
  | j + 1, hj => by
      have hsplit : m - 4 + (j + 1) = (m - 4 + j) + 1 := by omega
      rw [hsplit, cheapSum_succ, cheapSumB_one_p3 h3 hm j (by omega),
        cheapRowNat_dvd_gt h3 (by omega),
        show (eVec (rotPlusPlus 1) : TerminalQ m) = (1, 0) from rfl,
        Prod.mk_add_mk, add_zero, Nat.cast_succ]

theorem cheapSumB_two_p3 (h3 : m % 3 = 0) (hm : 4 ≤ m) :
    ∀ j, j ≤ 3 →
      cheapSum m 2 (m - 4 + j)
        = (((1 : ZMod m), ((j : Nat) : ZMod m)))
  | 0, _ => by
      rw [Nat.add_zero, cheapSumB_two_p2 h3 hm, Nat.cast_zero]
  | j + 1, hj => by
      have hsplit : m - 4 + (j + 1) = (m - 4 + j) + 1 := by omega
      rw [hsplit, cheapSum_succ, cheapSumB_two_p3 h3 hm j (by omega),
        cheapRowNat_dvd_gt h3 (by omega),
        show (eVec (rotPlusPlus 2) : TerminalQ m) = (0, 1) from rfl,
        Prod.mk_add_mk, add_zero, Nat.cast_succ]

end CheapSum

/-! ## The drift constants `u_c = e_c + v_c` -/

section Drift

variable {m : Nat}

/-- The conjugated per-color drift `u_c` in pair coordinates, exactly the
table of `docs/WILDE_SEARCH_20260610.md` §3.2 (and the script's printed
`u`): `3 ∤ m`: `((1,1), (m−2,1), (1,m−2))`; `3 ∣ m`:
`((m−4,1), (3,m−4), (1,3))`. -/
def driftPair (m : Nat) (c : Fin 3) : TerminalQ m :=
  if m % 3 = 0 then
    if c = 0 then (((m - 4 : Nat) : ZMod m), 1)
    else if c = 1 then (3, ((m - 4 : Nat) : ZMod m))
    else (1, 3)
  else
    if c = 0 then (1, 1)
    else if c = 1 then (((m - 2 : Nat) : ZMod m), 1)
    else (1, ((m - 2 : Nat) : ZMod m))

theorem driftPair_dvd_zero (h3 : m % 3 = 0) :
    driftPair m 0 = (((m - 4 : Nat) : ZMod m), 1) := by
  unfold driftPair
  rw [if_pos h3, if_pos rfl]

theorem driftPair_dvd_one (h3 : m % 3 = 0) :
    driftPair m 1 = (3, ((m - 4 : Nat) : ZMod m)) := by
  unfold driftPair
  rw [if_pos h3, if_neg (by decide : ¬(1 : Fin 3) = 0), if_pos rfl]

theorem driftPair_dvd_two (h3 : m % 3 = 0) :
    driftPair m 2 = ((1 : ZMod m), 3) := by
  unfold driftPair
  rw [if_pos h3, if_neg (by decide : ¬(2 : Fin 3) = 0),
    if_neg (by decide : ¬(2 : Fin 3) = 1)]

theorem driftPair_ne_zero (h3 : m % 3 ≠ 0) :
    driftPair m 0 = ((1 : ZMod m), 1) := by
  unfold driftPair
  rw [if_neg h3, if_pos rfl]

theorem driftPair_ne_one (h3 : m % 3 ≠ 0) :
    driftPair m 1 = (((m - 2 : Nat) : ZMod m), 1) := by
  unfold driftPair
  rw [if_neg h3, if_neg (by decide : ¬(1 : Fin 3) = 0), if_pos rfl]

theorem driftPair_ne_two (h3 : m % 3 ≠ 0) :
    driftPair m 2 = ((1 : ZMod m), ((m - 2 : Nat) : ZMod m)) := by
  unfold driftPair
  rw [if_neg h3, if_neg (by decide : ¬(2 : Fin 3) = 0),
    if_neg (by decide : ¬(2 : Fin 3) = 1)]

theorem eVec_add_cheapSum_zero (hm : 4 ≤ m) :
    eVec 0 + cheapSum m 0 (m - 1) = driftPair m 0 := by
  by_cases h3 : m % 3 = 0
  · have h14 : m - 1 = m - 4 + 3 := by omega
    rw [h14, cheapSumB_zero_p3 h3 hm 3 le_rfl, driftPair_dvd_zero h3,
      show (eVec 0 : TerminalQ m) = (1, 0) from rfl, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor
    · have h54 : m - 4 = m - 5 + 1 := by omega
      rw [h54, Nat.cast_succ]
      ring
    · rw [zero_add]
  · have h12 : m - 1 = m - 2 + 1 := by omega
    rw [h12, cheapSumA_zero h3 (m - 2), driftPair_ne_zero h3,
      show (eVec 0 : TerminalQ m) = (1, 0) from rfl, Prod.mk_add_mk,
      add_zero, zero_add]

theorem eVec_add_cheapSum_one (hm : 4 ≤ m) :
    eVec 1 + cheapSum m 1 (m - 1) = driftPair m 1 := by
  by_cases h3 : m % 3 = 0
  · have h14 : m - 1 = m - 4 + 3 := by omega
    rw [h14, cheapSumB_one_p3 h3 hm 3 le_rfl, driftPair_dvd_one h3,
      show (eVec 1 : TerminalQ m) = (0, 1) from rfl, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor
    · rw [zero_add, Nat.cast_ofNat]
    · have h54 : m - 4 = m - 5 + 1 := by omega
      rw [h54, Nat.cast_succ]
      ring
  · have h12 : m - 1 = m - 2 + 1 := by omega
    rw [h12, cheapSumA_one h3 (m - 2), driftPair_ne_one h3,
      show (eVec 1 : TerminalQ m) = (0, 1) from rfl, Prod.mk_add_mk,
      add_zero, zero_add]

theorem eVec_add_cheapSum_two (hm : 4 ≤ m) :
    eVec 2 + cheapSum m 2 (m - 1) = driftPair m 2 := by
  by_cases h3 : m % 3 = 0
  · have h14 : m - 1 = m - 4 + 3 := by omega
    rw [h14, cheapSumB_two_p3 h3 hm 3 le_rfl, driftPair_dvd_two h3,
      show (eVec 2 : TerminalQ m) = (0, 0) from rfl, Prod.mk_add_mk,
      zero_add, zero_add, Nat.cast_ofNat]
  · have h12 : m - 1 = m - 2 + 1 := by omega
    rw [h12, cheapSumA_two h3 (m - 2), driftPair_ne_two h3,
      show (eVec 2 : TerminalQ m) = (0, 0) from rfl, Prod.mk_add_mk,
      zero_add, zero_add]

/-- The drift table, color-uniform form: `e_c + v_c = u_c`. -/
theorem eVec_add_cheapSum (hm : 4 ≤ m) (c : Fin 3) :
    eVec c + cheapSum m c (m - 1) = driftPair m c := by
  fin_cases c
  · exact eVec_add_cheapSum_zero hm
  · exact eVec_add_cheapSum_one hm
  · exact eVec_add_cheapSum_two hm

end Drift

/-! ## The return map and its reduction to the core statement -/

section ReturnMap

variable {m : Nat} [NeZero m]

/-- The cheap collapse vector `v_c = Σ_{t<m−1} e_{σ_t(c)}` in root
coordinates. -/
def cheapVec (m : Nat) [NeZero m] (c : Fin 3) : RootState m :=
  pairRoot (cheapSum m c (m - 1))

/-- The conjugated drift `u_c = e_c + v_c` in root coordinates. -/
def driftVec (m : Nat) [NeZero m] (c : Fin 3) : RootState m :=
  pairRoot (driftPair m c)

theorem stepVec_add_cheapVec (hm : 4 ≤ m) (c : Fin 3) :
    stepVec c + cheapVec m c = driftVec m c := by
  unfold cheapVec driftVec
  rw [← eVec_add_cheapSum hm c, pairRoot_add, pairRoot_eVec]

/-- The per-color schedule return map `R_c` (layer `0` applied first, the
wild layer `m − 1` last). -/
def railReturn (m : Nat) [NeZero m] (c : TorusColor 3) :
    RootState m → RootState m :=
  (railSchedule m).returnMap c

theorem railSchedule_prefixMap_zero (c : TorusColor 3) (w : RootState m) :
    (railSchedule m).prefixMap c 0 w = w := rfl

theorem railSchedule_prefixMap_succ (c : TorusColor 3) (k : Nat)
    (w : RootState m) :
    (railSchedule m).prefixMap c (k + 1) w
      = (railSchedule m).layerMap ((k : Nat) : ZMod m) c
          ((railSchedule m).prefixMap c k w) := rfl

/-- Cheap collapse: the first `k ≤ m − 1` layers compose to the translation
by the partial cheap sum. -/
theorem prefixMap_cheap (c : TorusColor 3) :
    ∀ k, k ≤ m - 1 → ∀ w : RootState m,
      (railSchedule m).prefixMap c k w = w + pairRoot (cheapSum m c k)
  | 0, _, w => by
      rw [railSchedule_prefixMap_zero, cheapSum_zero, pairRoot_zero,
        add_zero]
  | k + 1, hk, w => by
      have hval : ((k : Nat) : ZMod m).val = k :=
        ZMod.val_natCast_of_lt (by omega)
      have hne : ((k : Nat) : ZMod m).val ≠ m - 1 := by
        rw [hval]
        omega
      rw [railSchedule_prefixMap_succ, prefixMap_cheap c k (by omega) w,
        railSchedule_layerMap_apply, railRow_of_cheap hne, hval,
        cheapSum_succ, pairRoot_add, pairRoot_eVec, add_assoc]

/-- **The return reduction**: the schedule return is the wild layer applied
after the cheap translation, `R_c w = ρ_c(w + v_c) + e_c`. -/
theorem railReturn_apply (hm : 4 ≤ m) (c : TorusColor 3) (w : RootState m) :
    railReturn m c w = rhoRoot c (w + cheapVec m c) + stepVec c := by
  have hval : (((m - 1 : Nat)) : ZMod m).val = m - 1 :=
    ZMod.val_natCast_of_lt (by omega)
  have h0 : railReturn m c w = (railSchedule m).prefixMap c m w := by
    change (railSchedule m).returnMap c w = _
    rw [RootFlatSchedule.returnMap_eq_prefixMap]
  have hsucc : m - 1 + 1 = m := by omega
  have h1 : (railSchedule m).prefixMap c m w
      = (railSchedule m).prefixMap c (m - 1 + 1) w := by
    rw [hsucc]
  rw [h0, h1, railSchedule_prefixMap_succ,
    prefixMap_cheap c (m - 1) le_rfl w, railSchedule_layerMap_wild hval c,
    show cheapVec m c = pairRoot (cheapSum m c (m - 1)) from rfl]

/-- The return reduction in composed form:
`R_c = (T_{e_c} ∘ ρ_c) ∘ T_{v_c}`. -/
theorem railReturn_eq (hm : 4 ≤ m) (c : TorusColor 3) :
    railReturn m c
      = (fun w : RootState m => rhoRoot c w + stepVec c)
          ∘ (fun w : RootState m => w + cheapVec m c) := by
  funext w
  rw [Function.comp_apply, railReturn_apply hm c w]

/-- **The module-3 handoff**: if the conjugated core map
`w ↦ ρ_c(w) + u_c` is a single `m²`-cycle, then so is the schedule return
`R_c`.  Conjugation is by the cheap translation `T_{v_c}`:
`T_{v_c} ∘ (R_c) ∘ T_{v_c}⁻¹ = T_{u_c} ∘ ρ_c` with `u_c = e_c + v_c`. -/
theorem railReturn_singleCycle_of_core (hm : 4 ≤ m) (c : TorusColor 3)
    (hcore : IsSingleCycleMap
      (fun w : RootState m => rhoRoot c w + driftVec m c)) :
    IsSingleCycleMap (railReturn m c) := by
  refine single_cycle_of_equiv_conj (Equiv.subRight (cheapVec m c))
    (railReturn m c) (fun w => rhoRoot c w + driftVec m c) hcore ?_
  intro x
  simp only [Equiv.subRight_apply, Equiv.subRight_symm_apply]
  rw [railReturn_apply hm c, sub_add_cancel, add_assoc,
    stepVec_add_cheapVec hm c]

/-- Final packaging stub for module 3: the rail-seam `dir` with RF1/RF2
proven here, and RF3 assembled from the three per-color core cyclicity
statements (the only remaining obligations). -/
def railCycleData (m : Nat) [NeZero m] (hm : 4 ≤ m)
    (h0 : IsSingleCycleMap
      (fun w : RootState m => rhoRoot 0 w + driftVec m 0))
    (h1 : IsSingleCycleMap
      (fun w : RootState m => rhoRoot 1 w + driftVec m 1))
    (h2 : IsSingleCycleMap
      (fun w : RootState m => rhoRoot 2 w + driftVec m 2)) :
    RootFlatCycle.RootFlatCycleData 2 m where
  dir := railDir m
  rowLatin := railSchedule_rowLatin m
  layerBijective := railSchedule_layerBijective hm
  returnsSingleCycle := by
    intro c
    fin_cases c
    · exact railReturn_singleCycle_of_core hm 0 h0
    · exact railReturn_singleCycle_of_core hm 1 h1
    · exact railReturn_singleCycle_of_core hm 2 h2

end ReturnMap

/-! ## Decide anchors at `m = 4`, `m = 6` (and drift tables at `8`, `12`)

These pin the layer assignment, the drift constants and sample return values
against `scripts/search_d3_even_dir.py construct --m {4,6}` (the script is
ground truth; the sample return values below are its `compose_return`
output). -/

section Anchors

-- Layer assignment, m = 4 (`3 ∤ m`): [ρ⁺, ρ⁺⁺, ρ⁺⁺, wild]; the probe cell
-- (0,1) is off all rails, so the wild row reads the identity there.
example : (List.range 4).map
      (fun t => railDir 4 ((t : Nat) : ZMod 4) (pairRoot ((0 : ZMod 4), 1)) 0)
    = [1, 2, 2, 0] := by decide

-- Layer assignment, m = 6 (`3 ∣ m`): [id, ρ⁺, ρ⁺⁺, ρ⁺⁺, ρ⁺⁺, wild]; the
-- probe cell (4,4) is off all rails.
example : (List.range 6).map
      (fun t => railDir 6 ((t : Nat) : ZMod 6) (pairRoot ((4 : ZMod 6), 4)) 0)
    = [0, 1, 2, 2, 2, 0] := by decide

-- Drift constants u_c against the script (`3 ∤ m`: ((1,1),(m−2,1),(1,m−2));
-- `3 ∣ m`: ((m−4,1),(3,m−4),(1,3))).
example :
    driftPair 4 0 = (1, 1) ∧ driftPair 4 1 = (2, 1) ∧
      driftPair 4 2 = (1, 2) := by decide

example :
    driftPair 6 0 = (2, 1) ∧ driftPair 6 1 = (3, 2) ∧
      driftPair 6 2 = (1, 3) := by decide

example :
    driftPair 8 0 = (1, 1) ∧ driftPair 8 1 = (6, 1) ∧
      driftPair 8 2 = (1, 6) := by decide

example :
    driftPair 12 0 = (8, 1) ∧ driftPair 12 1 = (3, 8) ∧
      driftPair 12 2 = (1, 3) := by decide

-- Independent cross-check of the closed-form drift theorem at the anchors.
example : ∀ c : Fin 3, eVec c + cheapSum 4 c 3 = driftPair 4 c := by decide

example : ∀ c : Fin 3, eVec c + cheapSum 6 c 5 = driftPair 6 c := by decide

-- Sample return values, m = 4 (script `compose_return`).
example :
    rootPair (railReturn 4 0 (pairRoot ((0 : ZMod 4), 0))) = (1, 1) ∧
      rootPair (railReturn 4 0 (pairRoot ((1 : ZMod 4), 2))) = (2, 3) ∧
      rootPair (railReturn 4 1 (pairRoot ((0 : ZMod 4), 0))) = (2, 0) ∧
      rootPair (railReturn 4 1 (pairRoot ((3 : ZMod 4), 1))) = (1, 2) ∧
      rootPair (railReturn 4 2 (pairRoot ((0 : ZMod 4), 0))) = (1, 2) ∧
      rootPair (railReturn 4 2 (pairRoot ((2 : ZMod 4), 3))) = (3, 1) := by
  decide

-- Sample return values, m = 6.
example :
    rootPair (railReturn 6 0 (pairRoot ((0 : ZMod 6), 0))) = (2, 1) ∧
      rootPair (railReturn 6 0 (pairRoot ((1 : ZMod 6), 2))) = (3, 3) ∧
      rootPair (railReturn 6 1 (pairRoot ((0 : ZMod 6), 0))) = (3, 2) ∧
      rootPair (railReturn 6 1 (pairRoot ((3 : ZMod 6), 1))) = (0, 3) ∧
      rootPair (railReturn 6 2 (pairRoot ((0 : ZMod 6), 0))) = (1, 3) ∧
      rootPair (railReturn 6 2 (pairRoot ((2 : ZMod 6), 3))) = (3, 0) := by
  decide

end Anchors

end D3EvenRailSchedule
end V28Hard
end EvenV11
