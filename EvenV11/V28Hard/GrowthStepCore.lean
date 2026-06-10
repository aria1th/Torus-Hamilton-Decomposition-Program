import EvenV11.V28Hard.HEDBaseWitnesses
import EvenV11.V28Hard.CompletionTower

/-!
# G4 — `GrowthStepCore`: the growth step `HEDWitness n m → HEDWitness (n+2) m`

Growth-engine slot G4 (`docs/GROWTH_ENGINE_DESIGN_20260610.md`; paper
`prop:chained-two-hole`/`prop:paired-growth` of
`/data/angel/repos/etc/even_modulus_rewrite_20260610/subtex/high_even_growth.tex`
generalized per the chain datum `subtex/high_even_chain_datum.tex`).

## What is closed here, and what remains (the numeric gate came first)

The numeric gate (`scripts/growth_step_replay.py --growth-step`, replaying
`7 → 9` at `m = 4` over the dimension-7 witness blob behind `hedWitness74`)
validates EXACTLY the construction formalized below:

* the child schedule = the old schedule embedded along the chart with the two
  new leaf coordinates appended, the new colors reading their own leaves, plus
  two crossing families realizing the unit carries —
  `(last ↔ leaf₀)` swaps on z-free planes `{x⁰_c} × (ZMod m)²` at layers
  `t⁰_c`, and `(last ↔ leaf₁)` swaps on `z₀`-pinned lines
  `{x¹_c} × {ξ_c} × ZMod m` at layers `t¹_c < t⁰_c`, one pair per old color
  `c`, placed at points where `c` reads the zero-step direction
  (`lem:four-point-one-point-carry`'s one-point carry at the closing column);
* **RF1 and RF2 hold for every color** (proven parametrically below;
  machine-verified at the gate);
* **the per-color return decomposition for every OLD color**
  (machine-verified pointwise at the gate; the heart of this file):

  `R'_c (x, z₀, z₁) = (R_c x, z₀ + κ⁰_c x, z₁ + κ¹_c x z₀)`

  with `κ⁰_c` supported at the unique orbit position crossing the plane and
  `κ¹_c` at the pinned line — hence every old-color child return is a single
  `K·m²`-cycle, by the tower `CompletionTower.rankEquiv_of_singleCycle`
  (rank from the OLD return's RF3) → `UnitCarry.rankUnitCarrySingleCycle`
  (carry sum `= 1`, a unit), applied twice (`additiveSkewMap` shapes).
  All seven old colors PASS at the gate with carry sums `(1,1)` and single
  `65536`-cycles, and the selector/reserve transports PASS.

* **the two NEW colors are the open core.**  Under this child `dir` their
  returns are `z`-translations (the design-doc Part-1.3 finding: the naive
  block-diagonal extension fails RF3 for the new colors — confirmed at the
  gate: cycle type `4 × 16384`).  The gate's `--core-findings` subcommand
  records the machine-checked negative results that scope what any repair
  must look like over a black-box input schedule: on the `(7,4)` blob,
  0/9576 same-layer `m`-letter role products, 0/28 dropped-letter words and
  0/252 donated two-layer words are single `K`-cycles, and a donated-cycles
  parity identity (sign(Φ)·sign(Ψ) = sign(R) is odd, so Φ and Ψ cannot both
  be single `K`-cycles for even `K`) refutes every single-partner handover.
  The new-color realization therefore stays a precisely shaped obligation
  (`GrowthRealization`): a child `dir⋆` that (i) is row-Latin, (ii) is
  layer-bijective, (iii) has the SAME old-color return maps as the
  constructed schedule (so the closed decomposition applies verbatim), and
  (iv) has single-cycle returns at the two new colors.  `GrowthStep` is then
  assembled from the closed content plus these hypotheses — never a `sorry`.

The witness-level fields (selector transport with leaf pins `(2,2)`, reserve
transport `n+4 → n+6` with the two renewal sites at leaf value `3`
(`lem:growth-reserve-transport` / `lem:growth-leaf-fiber-room`), trace
avoidance via the leaf values `{0,1}` vs `{2,3}` (`4 ≤ m`), and the NEXT
chain fields — the ordinary paired interface of `GuideLocality` in the
output chart `ZMod (n+5)` with carrier `{5,6,7}`
(`lem:chain-output-assembly`)) are constructed below from the placement's
selector-avoidance clauses.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace EvenV11
namespace V28Hard
namespace GrowthStepCore

open Shared StandardRootFlatLift RootFlatCycle

variable {n m : Nat}

/-! ## Part 1: the grown state space and its chart -/

/-- Product form of the grown root state: old state × leaf₀ × leaf₁. -/
abbrev GrowState (n m : Nat) : Type :=
  RootState n m × ZMod m × ZMod m

/-- Append the two leaf coordinates to an old root state. -/
def embedSt (x : RootState n m) (z₀ z₁ : ZMod m) : RootState (n + 2) m :=
  Fin.snoc (Fin.snoc x z₀) z₁

theorem embedSt_apply_lt (x : RootState n m) (z₀ z₁ : ZMod m)
    {j : Fin (n + 2)} {i : Fin n} (h : (j : Nat) = (i : Nat)) :
    embedSt x z₀ z₁ j = x i := by
  have hj : j = i.castSucc.castSucc := Fin.ext (by simpa using h)
  rw [hj, embedSt, Fin.snoc_castSucc, Fin.snoc_castSucc]

theorem embedSt_apply_z0 (x : RootState n m) (z₀ z₁ : ZMod m)
    {j : Fin (n + 2)} (h : (j : Nat) = n) :
    embedSt x z₀ z₁ j = z₀ := by
  have hj : j = (Fin.last n).castSucc := by
    apply Fin.ext
    simpa using h
  rw [hj, embedSt, Fin.snoc_castSucc, Fin.snoc_last]

theorem embedSt_apply_z1 (x : RootState n m) (z₀ z₁ : ZMod m)
    {j : Fin (n + 2)} (h : (j : Nat) = n + 1) :
    embedSt x z₀ z₁ j = z₁ := by
  have hj : j = Fin.last (n + 1) := by
    apply Fin.ext
    simpa using h
  rw [hj, embedSt, Fin.snoc_last]

/-- The chart between the product form and the grown root state. -/
def growEquiv : GrowState n m ≃ RootState (n + 2) m where
  toFun a := embedSt a.1 a.2.1 a.2.2
  invFun w :=
    (fun i => w ⟨i, by omega⟩, w ⟨n, by omega⟩, w ⟨n + 1, by omega⟩)
  left_inv := by
    rintro ⟨x, z₀, z₁⟩
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i
      exact embedSt_apply_lt x z₀ z₁ (j := ⟨i, by omega⟩) rfl
    · exact embedSt_apply_z0 x z₀ z₁ rfl
    · exact embedSt_apply_z1 x z₀ z₁ rfl
  right_inv := by
    intro w
    funext j
    dsimp only
    rcases lt_trichotomy (j : Nat) n with h | h | h
    · rw [embedSt_apply_lt _ _ _ (i := ⟨(j : Nat), h⟩) rfl]
    · rw [embedSt_apply_z0 _ _ _ h]
      exact congrArg w (Fin.ext h.symm)
    · have h1 : (j : Nat) = n + 1 := by
        have := j.isLt
        omega
      rw [embedSt_apply_z1 _ _ _ h1]
      exact congrArg w (Fin.ext h1.symm)

@[simp] theorem growEquiv_apply (a : GrowState n m) :
    growEquiv a = embedSt a.1 a.2.1 a.2.2 := rfl

theorem embedSt_injective2 {x y : RootState n m} {a₀ a₁ b₀ b₁ : ZMod m}
    (h : embedSt x a₀ a₁ = embedSt y b₀ b₁) :
    x = y ∧ a₀ = b₀ ∧ a₁ = b₁ := by
  have h' : (growEquiv (n := n) (m := m)) (x, a₀, a₁) = growEquiv (y, b₀, b₁) := h
  have := growEquiv.injective h'
  exact ⟨congrArg Prod.fst this,
    congrArg (fun p => p.2.1) this, congrArg (fun p => p.2.2) this⟩

/-- Direction/color chart `Fin (n+1) → Fin (n+3)`: old coordinate directions
keep their index, the old zero-step direction goes to the new zero-step. -/
def ι (i : Fin (n + 1)) : Fin (n + 3) :=
  if h : (i : Nat) < n then ⟨i, by omega⟩ else Fin.last (n + 2)

/-- First new leaf direction/color (steps coordinate `n`). -/
def leaf0 : Fin (n + 3) := ⟨n, by omega⟩

/-- Second new leaf direction/color (steps coordinate `n + 1`). -/
def leaf1 : Fin (n + 3) := ⟨n + 1, by omega⟩

theorem ι_val (i : Fin (n + 1)) :
    ((ι i : Fin (n + 3)) : Nat) = if (i : Nat) < n then (i : Nat) else n + 2 := by
  rw [ι]
  by_cases h : (i : Nat) < n
  · rw [dif_pos h, if_pos h]
  · rw [dif_neg h, if_neg h]
    rfl

theorem ι_val_ne_n (i : Fin (n + 1)) : ((ι i : Fin (n + 3)) : Nat) ≠ n := by
  rw [ι_val]
  by_cases h : (i : Nat) < n
  · simp only [if_pos h]
    omega
  · simp only [if_neg h]
    omega

theorem ι_val_ne_n1 (i : Fin (n + 1)) :
    ((ι i : Fin (n + 3)) : Nat) ≠ n + 1 := by
  rw [ι_val]
  by_cases h : (i : Nat) < n
  · simp only [if_pos h]
    omega
  · simp only [if_neg h]
    omega

theorem ι_injective : Function.Injective (ι (n := n)) := by
  intro a b hab
  have hv := congrArg Fin.val hab
  rw [ι_val, ι_val] at hv
  have ha := a.isLt
  have hb := b.isLt
  apply Fin.ext
  by_cases h1 : (a : Nat) < n <;> by_cases h2 : (b : Nat) < n <;>
    simp [h1, h2] at hv <;> omega

theorem ι_ne_leaf0 (i : Fin (n + 1)) : ι i ≠ leaf0 := by
  intro h
  exact ι_val_ne_n i (congrArg Fin.val h)

theorem ι_ne_leaf1 (i : Fin (n + 1)) : ι i ≠ leaf1 := by
  intro h
  exact ι_val_ne_n1 i (congrArg Fin.val h)

theorem leaf0_ne_leaf1 : (leaf0 : Fin (n + 3)) ≠ leaf1 := by
  intro h
  have := congrArg Fin.val h
  simp [leaf0, leaf1] at this

theorem last_ne_leaf0' : ¬ ((leaf0 : Fin (n + 3)) = Fin.last (n + 2)) := by
  intro h
  have := congrArg Fin.val h
  simp [leaf0, Fin.last] at this

theorem last_ne_leaf1' : ¬ ((leaf1 : Fin (n + 3)) = Fin.last (n + 2)) := by
  intro h
  have := congrArg Fin.val h
  simp only [leaf1, Fin.val_last] at this
  omega

theorem ι_last_val : ((ι (Fin.last n) : Fin (n + 3)) : Nat) = n + 2 := by
  rw [ι_val]
  simp

/-- Color trichotomy in the grown chart. -/
theorem color_cases (c' : Fin (n + 3)) :
    (∃ c : Fin (n + 1), c' = ι c) ∨ c' = leaf0 ∨ c' = leaf1 := by
  rcases lt_trichotomy (c' : Nat) n with h | h | h
  · refine Or.inl ⟨⟨c', by omega⟩, ?_⟩
    apply Fin.ext
    rw [ι_val]
    simp [h]
  · exact Or.inr (Or.inl (Fin.ext (by simpa [leaf0] using h)))
  · by_cases h2 : (c' : Nat) = n + 1
    · exact Or.inr (Or.inr (Fin.ext (by simpa [leaf1] using h2)))
    · refine Or.inl ⟨Fin.last n, ?_⟩
      apply Fin.ext
      rw [ι_last_val]
      have := c'.isLt
      omega

/-! ## Part 2: the product-side step and its conjugation to `rootStep` -/

/-- Product-side step: old coordinate directions act on the old state, the
two leaves step their own coordinate, the new zero-step does nothing. -/
def growStepP (δ : Fin (n + 3)) (a : GrowState n m) : GrowState n m :=
  if h : (δ : Nat) < n then
    (rootStep ⟨δ, by omega⟩ a.1, a.2.1, a.2.2)
  else if (δ : Nat) = n then
    (a.1, a.2.1 + 1, a.2.2)
  else if (δ : Nat) = n + 1 then
    (a.1, a.2.1, a.2.2 + 1)
  else
    (a.1, a.2.1, a.2.2)

/-- `rootStep` through the value of the direction index. -/
theorem rootStep_apply_val {N : Nat} (i : Fin (N + 1)) (w : RootState N m)
    (j : Fin N) :
    rootStep i w j = if (i : Nat) = (j : Nat) then w j + 1 else w j := by
  rw [rootStep]
  by_cases h : (i : Nat) = (j : Nat)
  · rw [if_pos (Fin.ext (by simpa using h)), if_pos h]
  · rw [if_neg (fun hc => h (by simpa using congrArg Fin.val hc)), if_neg h]

@[simp] theorem growStepP_ι (v : Fin (n + 1)) (a : GrowState n m) :
    growStepP (ι v) a = (rootStep v a.1, a.2.1, a.2.2) := by
  by_cases h : (v : Nat) < n
  · have hlt : ((ι v : Fin (n + 3)) : Nat) < n := by
      rw [ι_val, if_pos h]; exact h
    rw [growStepP, dif_pos hlt]
    refine Prod.ext ?_ rfl
    funext j
    dsimp only
    rw [rootStep_apply_val, rootStep_apply_val]
    have : ((⟨((ι v : Fin (n + 3)) : Nat), by omega⟩ : Fin (n + 1)) : Nat)
        = (v : Nat) := by
      rw [ι_val, if_pos h]
    rw [this]
  · have hv : (v : Nat) = n := by
      have := v.isLt
      omega
    have h2 : ((ι v : Fin (n + 3)) : Nat) = n + 2 := by
      rw [ι_val, if_neg h]
    rw [growStepP, dif_neg (by omega), if_neg (by omega), if_neg (by omega)]
    refine Prod.ext ?_ rfl
    funext j
    dsimp only
    rw [rootStep_apply_val, if_neg (show ¬ ((v : Nat) = (j : Nat)) by omega)]

@[simp] theorem growStepP_leaf0 (a : GrowState n m) :
    growStepP (leaf0 : Fin (n + 3)) a = (a.1, a.2.1 + 1, a.2.2) := by
  have h0 : ¬ ((leaf0 : Fin (n + 3)) : Nat) < n := by simp [leaf0]
  have h1 : ((leaf0 : Fin (n + 3)) : Nat) = n := rfl
  rw [growStepP, dif_neg h0, if_pos h1]

@[simp] theorem growStepP_leaf1 (a : GrowState n m) :
    growStepP (leaf1 : Fin (n + 3)) a = (a.1, a.2.1, a.2.2 + 1) := by
  have h0 : ¬ ((leaf1 : Fin (n + 3)) : Nat) < n := by simp [leaf1]
  have h1 : ¬ ((leaf1 : Fin (n + 3)) : Nat) = n := by simp [leaf1]
  have h2 : ((leaf1 : Fin (n + 3)) : Nat) = n + 1 := rfl
  rw [growStepP, dif_neg h0, if_neg h1, if_pos h2]

/-- The chart conjugates the product step to the standard-lift `rootStep`. -/
theorem growStep_conj (δ : Fin (n + 3)) (a : GrowState n m) :
    growEquiv (growStepP δ a) = rootStep δ (growEquiv a) := by
  rcases a with ⟨x, z₀, z₁⟩
  rcases color_cases δ with ⟨v, rfl⟩ | rfl | rfl
  · rw [growStepP_ι]
    funext j
    rw [growEquiv_apply, growEquiv_apply,
      rootStep_apply_val (ι v) (embedSt x z₀ z₁) j]
    dsimp only
    rcases lt_trichotomy (j : Nat) n with hj | hj | hj
    · rw [embedSt_apply_lt _ _ _ (i := ⟨(j : Nat), hj⟩) rfl,
        embedSt_apply_lt _ _ _ (i := ⟨(j : Nat), hj⟩) rfl,
        rootStep_apply_val]
      by_cases hv : (v : Nat) = (j : Nat)
      · have hι : ((ι v : Fin (n + 3)) : Nat) = (j : Nat) := by
          rw [ι_val, if_pos (by omega)]
          exact hv
        rw [if_pos hv, if_pos hι]
      · have hι : ¬ ((ι v : Fin (n + 3)) : Nat) = (j : Nat) := by
          rw [ι_val]
          by_cases h : (v : Nat) < n
          · rw [if_pos h]; exact hv
          · rw [if_neg h]; omega
        rw [if_neg hv, if_neg hι]
    · rw [embedSt_apply_z0 _ _ _ hj, embedSt_apply_z0 _ _ _ hj,
        if_neg (by rw [hj]; exact ι_val_ne_n v)]
    · have hj1 : (j : Nat) = n + 1 := by
        have := j.isLt
        omega
      rw [embedSt_apply_z1 _ _ _ hj1, embedSt_apply_z1 _ _ _ hj1,
        if_neg (by rw [hj1]; exact ι_val_ne_n1 v)]
  · rw [growStepP_leaf0]
    funext j
    rw [growEquiv_apply, growEquiv_apply,
      rootStep_apply_val (leaf0) (embedSt x z₀ z₁) j]
    dsimp only
    rcases lt_trichotomy (j : Nat) n with hj | hj | hj
    · rw [embedSt_apply_lt _ _ _ (i := ⟨(j : Nat), hj⟩) rfl,
        embedSt_apply_lt _ _ _ (i := ⟨(j : Nat), hj⟩) rfl,
        if_neg (show ¬ ((leaf0 : Fin (n + 3)) : Nat) = (j : Nat) by
          simp only [leaf0]
          omega)]
    · rw [embedSt_apply_z0 _ _ _ hj, embedSt_apply_z0 _ _ _ hj,
        if_pos (show ((leaf0 : Fin (n + 3)) : Nat) = (j : Nat) by
          simp only [leaf0]
          omega)]
    · have hj1 : (j : Nat) = n + 1 := by
        have := j.isLt
        omega
      rw [embedSt_apply_z1 _ _ _ hj1, embedSt_apply_z1 _ _ _ hj1,
        if_neg (show ¬ ((leaf0 : Fin (n + 3)) : Nat) = (j : Nat) by
          simp only [leaf0]
          omega)]
  · rw [growStepP_leaf1]
    funext j
    rw [growEquiv_apply, growEquiv_apply,
      rootStep_apply_val (leaf1) (embedSt x z₀ z₁) j]
    dsimp only
    rcases lt_trichotomy (j : Nat) n with hj | hj | hj
    · rw [embedSt_apply_lt _ _ _ (i := ⟨(j : Nat), hj⟩) rfl,
        embedSt_apply_lt _ _ _ (i := ⟨(j : Nat), hj⟩) rfl,
        if_neg (show ¬ ((leaf1 : Fin (n + 3)) : Nat) = (j : Nat) by
          simp only [leaf1]
          omega)]
    · rw [embedSt_apply_z0 _ _ _ hj, embedSt_apply_z0 _ _ _ hj,
        if_neg (show ¬ ((leaf1 : Fin (n + 3)) : Nat) = (j : Nat) by
          simp only [leaf1]
          omega)]
    · have hj1 : (j : Nat) = n + 1 := by
        have := j.isLt
        omega
      rw [embedSt_apply_z1 _ _ _ hj1, embedSt_apply_z1 _ _ _ hj1,
        if_pos (show ((leaf1 : Fin (n + 3)) : Nat) = (j : Nat) by
          simp only [leaf1]
          omega)]

/-! ## Part 3: the placement and the constructed child schedule

One `(last ↔ leaf₀)` crossing plane and one `(last ↔ leaf₁)` crossing line
per old color, at points where the color reads the zero-step direction.
`order` (the line layer strictly precedes the plane layer) makes the
`z₁`-crossing test the original `z₀`; `disjointPairs` keeps the two swap
families apart.  This is `lem:four-point-one-point-carry`'s one-point carry,
realized at the closing column of the chain datum's growth rows. -/

variable [NeZero m]

/-- Crossing placement for one growth step over the schedule `dir`. -/
structure GrowthPlacement (n m : Nat) [NeZero m]
    (dir : ZMod m → RootState n m →
      Shared.TorusColor (n + 1) → Shared.TorusDirection (n + 1)) :
    Type where
  /-- plane layer `t⁰_c` of the `z₀`-crossing of color `c`. -/
  t0 : Shared.TorusColor (n + 1) → Fin m
  /-- plane base point `x⁰_c`. -/
  x0 : Shared.TorusColor (n + 1) → RootState n m
  /-- line layer `t¹_c` of the `z₀`-pinned `z₁`-crossing. -/
  t1 : Shared.TorusColor (n + 1) → Fin m
  /-- line base point `x¹_c`. -/
  x1 : Shared.TorusColor (n + 1) → RootState n m
  /-- the `z₀`-pin `ξ_c` of the `z₁`-crossing line. -/
  pin : Shared.TorusColor (n + 1) → ZMod m
  /-- color `c` reads the zero-step direction at its plane point. -/
  read0 : ∀ c, dir ((t0 c : Nat) : ZMod m) (x0 c) c = Fin.last n
  /-- color `c` reads the zero-step direction at its line point. -/
  read1 : ∀ c, dir ((t1 c : Nat) : ZMod m) (x1 c) c = Fin.last n
  /-- the `z₁`-crossing happens strictly before the `z₀`-crossing. -/
  order : ∀ c, (t1 c : Nat) < (t0 c : Nat)
  /-- the line points and plane points are pairwise distinct. -/
  disjointPairs : ∀ c c', ¬ ((t1 c : Nat) = (t0 c' : Nat) ∧ x1 c = x0 c')

/-- A point lies on a crossing plane of layer `t`. -/
def onPlane {dir : ZMod m → RootState n m →
    Shared.TorusColor (n + 1) → Shared.TorusDirection (n + 1)}
    (P : GrowthPlacement n m dir) (t : ZMod m) (x : RootState n m) : Prop :=
  ∃ c, ((P.t0 c : Nat) : ZMod m) = t ∧ P.x0 c = x

/-- A point lies on a (pinned) crossing line of layer `t`. -/
def onLine {dir : ZMod m → RootState n m →
    Shared.TorusColor (n + 1) → Shared.TorusDirection (n + 1)}
    (P : GrowthPlacement n m dir) (t : ZMod m) (x : RootState n m)
    (z₀ : ZMod m) : Prop :=
  ∃ c, ((P.t1 c : Nat) : ZMod m) = t ∧ P.x1 c = x ∧ P.pin c = z₀

attribute [local instance] Classical.propDecidable

section Schedule

variable (data : RootFlatCycleData n m) (P : GrowthPlacement n m data.dir)

/-- The base row of the child schedule: old colors read their embedded old
reads, the new colors read their own leaves. -/
def baseRead (t : ZMod m) (x : RootState n m) (c' : Fin (n + 3)) :
    Fin (n + 3) :=
  if h : (c' : Nat) < n then ι (data.dir t x ⟨c', by omega⟩)
  else if (c' : Nat) = n then leaf0
  else if (c' : Nat) = n + 1 then leaf1
  else ι (data.dir t x (Fin.last n))

theorem baseRead_ι (t : ZMod m) (x : RootState n m) (c : Fin (n + 1)) :
    baseRead data t x (ι c) = ι (data.dir t x c) := by
  by_cases h : (c : Nat) < n
  · have hv : ((ι c : Fin (n + 3)) : Nat) < n := by
      rw [ι_val, if_pos h]; exact h
    rw [baseRead, dif_pos hv]
    congr 2
    apply Fin.ext
    rw [ι_val, if_pos h]
  · have hc : c = Fin.last n := by
      apply Fin.ext
      have := c.isLt
      simp only [Fin.val_last]
      omega
    subst hc
    have h2 : ((ι (Fin.last n) : Fin (n + 3)) : Nat) = n + 2 := ι_last_val
    rw [baseRead, dif_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem baseRead_leaf0 (t : ZMod m) (x : RootState n m) :
    baseRead data t x leaf0 = leaf0 := by
  rw [baseRead, dif_neg (by simp [leaf0]),
    if_pos (show ((leaf0 : Fin (n + 3)) : Nat) = n from rfl)]

theorem baseRead_leaf1 (t : ZMod m) (x : RootState n m) :
    baseRead data t x leaf1 = leaf1 := by
  have h0 : ¬ ((leaf1 : Fin (n + 3)) : Nat) < n := by simp [leaf1]
  have h1 : ¬ ((leaf1 : Fin (n + 3)) : Nat) = n := by simp [leaf1]
  rw [baseRead, dif_neg h0, if_neg h1,
    if_pos (show ((leaf1 : Fin (n + 3)) : Nat) = n + 1 from rfl)]

theorem baseRead_bijective (t : ZMod m) (x : RootState n m) :
    Function.Bijective (baseRead data t x) := by
  have hinj : Function.Injective (baseRead data t x) := by
    intro u v huv
    rcases color_cases u with ⟨a, rfl⟩ | rfl | rfl <;>
      rcases color_cases v with ⟨b, rfl⟩ | rfl | rfl
    · rw [baseRead_ι, baseRead_ι] at huv
      exact congrArg ι ((data.rowLatin t x).1 (ι_injective huv))
    · rw [baseRead_ι, baseRead_leaf0] at huv
      exact absurd huv (ι_ne_leaf0 _)
    · rw [baseRead_ι, baseRead_leaf1] at huv
      exact absurd huv (ι_ne_leaf1 _)
    · rw [baseRead_leaf0, baseRead_ι] at huv
      exact absurd huv.symm (ι_ne_leaf0 _)
    · rfl
    · rw [baseRead_leaf0, baseRead_leaf1] at huv
      exact absurd huv leaf0_ne_leaf1
    · rw [baseRead_leaf1, baseRead_ι] at huv
      exact absurd huv.symm (ι_ne_leaf1 _)
    · rw [baseRead_leaf1, baseRead_leaf0] at huv
      exact absurd huv.symm leaf0_ne_leaf1
    · rfl
  exact (Finite.injective_iff_bijective).mp hinj

/-- The child row: the base row composed with the crossing swaps —
`(last ↔ leaf₀)` on the planes, `(last ↔ leaf₁)` on the pinned lines. -/
noncomputable def growRead (t : ZMod m) (a : GrowState n m)
    (c' : Fin (n + 3)) : Fin (n + 3) :=
  let r := baseRead data t a.1 c'
  if onPlane P t a.1 then Equiv.swap (Fin.last (n + 2)) leaf0 r
  else if onLine P t a.1 a.2.1 then Equiv.swap (Fin.last (n + 2)) leaf1 r
  else r

/-- The constructed child schedule, on the product state space. -/
noncomputable def growthSchedule :
    Shared.RootFlatSchedule (Shared.TorusColor (n + 3))
      (Shared.TorusDirection (n + 3)) (GrowState n m) m where
  dir := fun t a c' => growRead data P t a c'
  step := growStepP

/-- **RF1 for the child schedule**: every row is a bijection. -/
theorem growthSchedule_rowLatin : (growthSchedule data P).rowLatin := by
  intro t a
  have hbase := baseRead_bijective data t a.1
  by_cases hp : onPlane P t a.1
  · have : (fun c' => (growthSchedule data P).dir t a c') =
        (Equiv.swap (Fin.last (n + 2)) leaf0) ∘ baseRead data t a.1 := by
      funext c'
      show growRead data P t a c' = _
      rw [growRead]
      simp only [if_pos hp]
      rfl
    rw [show (fun c' => (growthSchedule data P).dir t a c') =
        (Equiv.swap (Fin.last (n + 2)) leaf0) ∘ baseRead data t a.1 from this]
    exact (Equiv.swap _ _).bijective.comp hbase
  · by_cases hl : onLine P t a.1 a.2.1
    · have : (fun c' => (growthSchedule data P).dir t a c') =
          (Equiv.swap (Fin.last (n + 2)) leaf1) ∘ baseRead data t a.1 := by
        funext c'
        show growRead data P t a c' = _
        rw [growRead]
        simp only [if_neg hp, if_pos hl]
        rfl
      rw [this]
      exact (Equiv.swap _ _).bijective.comp hbase
    · have : (fun c' => (growthSchedule data P).dir t a c') =
          baseRead data t a.1 := by
        funext c'
        show growRead data P t a c' = _
        rw [growRead]
        simp only [if_neg hp, if_neg hl]
      rw [this]
      exact hbase

/-! ### Read shapes and layer-map decomposition -/

theorem ι_eq_last_iff (v : Fin (n + 1)) :
    ι v = Fin.last (n + 2) ↔ v = Fin.last n := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    rw [ι_val] at hv
    simp only [Fin.val_last] at hv
    apply Fin.ext
    simp only [Fin.val_last]
    by_cases h1 : (v : Nat) < n
    · rw [if_pos h1] at hv
      omega
    · have := v.isLt
      omega
  · intro h
    subst h
    apply Fin.ext
    rw [ι_last_val]
    simp

theorem growRead_ι (t : ZMod m) (a : GrowState n m) (c : Fin (n + 1)) :
    growRead data P t a (ι c) =
      if onPlane P t a.1 ∧ data.dir t a.1 c = Fin.last n then leaf0
      else if ¬ onPlane P t a.1 ∧ onLine P t a.1 a.2.1 ∧
          data.dir t a.1 c = Fin.last n then leaf1
      else ι (data.dir t a.1 c) := by
  rw [growRead]
  simp only [baseRead_ι]
  set v := data.dir t a.1 c with hv
  by_cases hp : onPlane P t a.1
  · simp only [if_pos hp]
    by_cases hl : v = Fin.last n
    · rw [if_pos ⟨hp, hl⟩]
      rw [show ι v = Fin.last (n + 2) from (ι_eq_last_iff v).mpr hl]
      exact Equiv.swap_apply_left _ _
    · rw [if_neg (fun h : onPlane P t a.1 ∧ data.dir t a.1 c = Fin.last n =>
          hl h.2),
        if_neg (fun h : ¬ onPlane P t a.1 ∧ _ ∧ _ => h.1 hp)]
      exact Equiv.swap_apply_of_ne_of_ne
        (fun h => hl ((ι_eq_last_iff v).mp h)) (ι_ne_leaf0 v)
  · simp only [if_neg hp]
    by_cases hl : onLine P t a.1 a.2.1
    · simp only [if_pos hl]
      by_cases hv' : v = Fin.last n
      · rw [if_neg (fun h : onPlane P t a.1 ∧ _ => hp h.1),
          if_pos ⟨hp, hl, hv'⟩]
        rw [show ι v = Fin.last (n + 2) from (ι_eq_last_iff v).mpr hv']
        exact Equiv.swap_apply_left _ _
      · rw [if_neg (fun h : onPlane P t a.1 ∧ data.dir t a.1 c = Fin.last n =>
            hp h.1),
          if_neg (fun h : ¬ onPlane P t a.1 ∧ _ ∧
            data.dir t a.1 c = Fin.last n => hv' h.2.2)]
        exact Equiv.swap_apply_of_ne_of_ne
          (fun h => hv' ((ι_eq_last_iff v).mp h)) (ι_ne_leaf1 v)
    · simp only [if_neg hl]
      rw [if_neg (fun h : onPlane P t a.1 ∧ _ => hp h.1),
        if_neg (fun h : ¬ _ ∧ onLine P t a.1 a.2.1 ∧ _ => hl h.2.1)]

theorem growRead_leaf0 (t : ZMod m) (a : GrowState n m) :
    growRead data P t a leaf0 =
      if onPlane P t a.1 then Fin.last (n + 2) else leaf0 := by
  rw [growRead]
  simp only [baseRead_leaf0]
  by_cases hp : onPlane P t a.1
  · simp only [if_pos hp]
    exact Equiv.swap_apply_right _ _
  · simp only [if_neg hp]
    by_cases hl : onLine P t a.1 a.2.1
    · simp only [if_pos hl]
      exact Equiv.swap_apply_of_ne_of_ne
        (fun h : (leaf0 : Fin (n + 3)) = Fin.last (n + 2) =>
          last_ne_leaf0' h)
        leaf0_ne_leaf1
    · simp only [if_neg hl]

theorem growRead_leaf1 (t : ZMod m) (a : GrowState n m) :
    growRead data P t a leaf1 =
      if ¬ onPlane P t a.1 ∧ onLine P t a.1 a.2.1 then Fin.last (n + 2)
      else leaf1 := by
  rw [growRead]
  simp only [baseRead_leaf1]
  by_cases hp : onPlane P t a.1
  · simp only [if_pos hp,
      if_neg (fun h : ¬ onPlane P t a.1 ∧ onLine P t a.1 a.2.1 => h.1 hp)]
    refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
    · exact fun h : (leaf1 : Fin (n + 3)) = Fin.last (n + 2) =>
        last_ne_leaf1' h
    · exact fun h : (leaf1 : Fin (n + 3)) = leaf0 => leaf0_ne_leaf1 h.symm
  · simp only [if_neg hp]
    by_cases hl : onLine P t a.1 a.2.1
    · simp only [if_pos hl, if_pos (And.intro hp hl)]
      exact Equiv.swap_apply_right _ _
    · simp only [if_neg hl,
        if_neg (fun h : ¬ onPlane P t a.1 ∧ onLine P t a.1 a.2.1 => hl h.2)]

omit [NeZero m] in
theorem rootStep_last {N : Nat} (w : RootState N m) :
    rootStep (Fin.last N) w = w := by
  funext j
  rw [rootStep_apply_val, if_neg (by
    simp only [Fin.val_last]
    omega)]

theorem growth_layerMap_ι (t : ZMod m) (c : Fin (n + 1)) (a : GrowState n m) :
    (growthSchedule data P).layerMap t (ι c) a =
      ((RootFlatCycle.schedule data.dir).layerMap t c a.1,
       a.2.1 + (if onPlane P t a.1 ∧ data.dir t a.1 c = Fin.last n
         then 1 else 0),
       a.2.2 + (if ¬ onPlane P t a.1 ∧ onLine P t a.1 a.2.1 ∧
           data.dir t a.1 c = Fin.last n then 1 else 0)) := by
  show growStepP (growRead data P t a (ι c)) a = _
  rw [growRead_ι]
  by_cases h0 : onPlane P t a.1 ∧ data.dir t a.1 c = Fin.last n
  · rw [if_pos h0, if_pos h0, if_neg (fun h => h.1 h0.1), growStepP_leaf0]
    refine Prod.ext ?_ (Prod.ext (by simp) (by simp))
    show a.1 = _
    have : (RootFlatCycle.schedule data.dir).layerMap t c a.1 =
        rootStep (data.dir t a.1 c) a.1 := rfl
    rw [this, h0.2, rootStep_last]
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : ¬ onPlane P t a.1 ∧ onLine P t a.1 a.2.1 ∧
        data.dir t a.1 c = Fin.last n
    · rw [if_pos h1, if_pos h1, growStepP_leaf1]
      refine Prod.ext ?_ (Prod.ext (by simp) (by simp))
      show a.1 = _
      have : (RootFlatCycle.schedule data.dir).layerMap t c a.1 =
          rootStep (data.dir t a.1 c) a.1 := rfl
      rw [this, h1.2.2, rootStep_last]
    · rw [if_neg h1, if_neg h1, growStepP_ι]
      exact Prod.ext rfl (Prod.ext (by simp) (by simp))

theorem growth_layerMap_leaf0 (t : ZMod m) (a : GrowState n m) :
    (growthSchedule data P).layerMap t leaf0 a =
      (a.1, a.2.1 + (if onPlane P t a.1 then 0 else 1), a.2.2) := by
  show growStepP (growRead data P t a leaf0) a = _
  rw [growRead_leaf0]
  by_cases hp : onPlane P t a.1
  · rw [if_pos hp, if_pos hp]
    have : growStepP (Fin.last (n + 2)) a = (a.1, a.2.1, a.2.2) := by
      rw [growStepP, dif_neg (by simp [Fin.last]),
        if_neg (by simp [Fin.last]), if_neg (by simp [Fin.last])]
    rw [this]
    exact Prod.ext rfl (Prod.ext (by simp) rfl)
  · rw [if_neg hp, if_neg hp, growStepP_leaf0]

theorem growth_layerMap_leaf1 (t : ZMod m) (a : GrowState n m) :
    (growthSchedule data P).layerMap t leaf1 a =
      (a.1, a.2.1,
       a.2.2 + (if ¬ onPlane P t a.1 ∧ onLine P t a.1 a.2.1 then 0 else 1)) := by
  show growStepP (growRead data P t a leaf1) a = _
  rw [growRead_leaf1]
  by_cases h : ¬ onPlane P t a.1 ∧ onLine P t a.1 a.2.1
  · rw [if_pos h, if_pos h]
    have : growStepP (Fin.last (n + 2)) a = (a.1, a.2.1, a.2.2) := by
      rw [growStepP, dif_neg (by simp [Fin.last]),
        if_neg (by simp [Fin.last]), if_neg (by simp [Fin.last])]
    rw [this]
    exact Prod.ext rfl (Prod.ext rfl (by simp))
  · rw [if_neg h, if_neg h, growStepP_leaf1]

/-- Skew bijection combinator: an `X`-bijection with `z₀`/`z₁` additive
skews testing the original coordinates. -/
def prodSkewEquiv (F : RootState n m ≃ RootState n m)
    (g0 : RootState n m → ZMod m) (g1 : RootState n m → ZMod m → ZMod m) :
    GrowState n m ≃ GrowState n m where
  toFun a := (F a.1, a.2.1 + g0 a.1, a.2.2 + g1 a.1 a.2.1)
  invFun b :=
    (F.symm b.1, b.2.1 - g0 (F.symm b.1),
      b.2.2 - g1 (F.symm b.1) (b.2.1 - g0 (F.symm b.1)))
  left_inv := by
    rintro ⟨x, z₀, z₁⟩
    simp
  right_inv := by
    rintro ⟨y, w₀, w₁⟩
    simp

/-- **RF2 for the child schedule**, in every color. -/
theorem growthSchedule_layerBijective :
    (growthSchedule data P).layerBijective := by
  intro t c'
  classical
  rcases color_cases c' with ⟨c, rfl⟩ | rfl | rfl
  · have heq : (growthSchedule data P).layerMap t (ι c) =
        prodSkewEquiv
          (Equiv.ofBijective _ (data.layerBijective t c))
          (fun x => if onPlane P t x ∧ data.dir t x c = Fin.last n
            then 1 else 0)
          (fun x z₀ => if ¬ onPlane P t x ∧ onLine P t x z₀ ∧
            data.dir t x c = Fin.last n then 1 else 0) := by
      funext a
      rw [growth_layerMap_ι]
      rfl
    rw [heq]
    exact (prodSkewEquiv _ _ _).bijective
  · have heq : (growthSchedule data P).layerMap t leaf0 =
        prodSkewEquiv (Equiv.refl _)
          (fun x => if onPlane P t x then 0 else 1)
          (fun _ _ => 0) := by
      funext a
      rw [growth_layerMap_leaf0]
      show _ = (a.1, a.2.1 + _, a.2.2 + 0)
      rw [add_zero]
    rw [heq]
    exact (prodSkewEquiv _ _ _).bijective
  · have heq : (growthSchedule data P).layerMap t leaf1 =
        prodSkewEquiv (Equiv.refl _)
          (fun _ => 0)
          (fun x z₀ => if ¬ onPlane P t x ∧ onLine P t x z₀ then 0 else 1) := by
      funext a
      rw [growth_layerMap_leaf1]
      show _ = (a.1, a.2.1 + 0, a.2.2 + _)
      rw [add_zero]
    rw [heq]
    exact (prodSkewEquiv _ _ _).bijective

/-! ### The per-color return decomposition (old colors)

`R'_c (x, z₀, z₁) = (R_c x, z₀ + κ⁰_c x, z₁ + κ¹_c x z₀)` — the G4
decomposition, machine-validated pointwise by the numeric gate. -/

omit [NeZero m] in
theorem castFin_eq {a : Fin m} {k : Nat} (hk : k < m)
    (h : ((a : Nat) : ZMod m) = (k : ZMod m)) : (a : Nat) = k := by
  have hmod : (a : Nat) ≡ k [MOD m] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  exact Nat.ModEq.eq_of_lt_of_lt hmod a.isLt hk

/-- A crossing-plane hit of an old color is exactly its own crossing
(placement read + RF1 uniqueness). -/
theorem hits0_iff (c : Fin (n + 1)) {k : Nat} (hk : k < m)
    (y : RootState n m) :
    (onPlane P (k : ZMod m) y ∧ data.dir (k : ZMod m) y c = Fin.last n) ↔
      ((P.t0 c : Nat) = k ∧ y = P.x0 c) := by
  constructor
  · rintro ⟨⟨c2, hcast, hx⟩, hlast⟩
    have hread := P.read0 c2
    rw [hcast, hx] at hread
    have hcc : c = c2 := (data.rowLatin _ y).1 (hlast.trans hread.symm)
    subst hcc
    exact ⟨castFin_eq hk hcast, hx.symm⟩
  · rintro ⟨ht, hy⟩
    subst hy
    refine ⟨⟨c, by rw [ht], rfl⟩, ?_⟩
    have := P.read0 c
    rwa [ht] at this

/-- A pinned-line hit of an old color is exactly its own crossing; the line
points avoid all planes (`disjointPairs`). -/
theorem hits1_iff (c : Fin (n + 1)) {k : Nat} (hk : k < m)
    (y : RootState n m) (z : ZMod m) :
    (¬ onPlane P (k : ZMod m) y ∧ onLine P (k : ZMod m) y z ∧
        data.dir (k : ZMod m) y c = Fin.last n) ↔
      ((P.t1 c : Nat) = k ∧ y = P.x1 c ∧ z = P.pin c) := by
  constructor
  · rintro ⟨-, ⟨c2, hcast, hx, hpin⟩, hlast⟩
    have hread := P.read1 c2
    rw [hcast, hx] at hread
    have hcc : c = c2 := (data.rowLatin _ y).1 (hlast.trans hread.symm)
    subst hcc
    exact ⟨castFin_eq hk hcast, hx.symm, hpin.symm⟩
  · rintro ⟨ht, hy, hz⟩
    subst hy
    subst hz
    refine ⟨?_, ⟨c, by rw [ht], rfl, rfl⟩, ?_⟩
    · rintro ⟨c3, hcast3, hx3⟩
      exact P.disjointPairs c c3
        ⟨by rw [ht, castFin_eq hk hcast3], hx3.symm⟩
    · have := P.read1 c
      rwa [ht] at this

/-- **The prefix decomposition for old colors** — the inductive heart of the
return decomposition. -/
theorem growth_prefix_ι (c : Fin (n + 1)) :
    ∀ k : Nat, k ≤ m → ∀ a : GrowState n m,
      (growthSchedule data P).prefixMap (ι c) k a =
        ((RootFlatCycle.schedule data.dir).prefixMap c k a.1,
         a.2.1 + (if (P.t0 c : Nat) < k ∧
             (RootFlatCycle.schedule data.dir).prefixMap c (P.t0 c) a.1
               = P.x0 c then 1 else 0),
         a.2.2 + (if (P.t1 c : Nat) < k ∧
             (RootFlatCycle.schedule data.dir).prefixMap c (P.t1 c) a.1
               = P.x1 c ∧ a.2.1 = P.pin c then 1 else 0))
  | 0, _, a => by
      refine Prod.ext rfl (Prod.ext ?_ ?_)
      · show a.2.1 = a.2.1 + _
        rw [if_neg (by omega : ¬ ((P.t0 c : Nat) < 0 ∧ _)), add_zero]
      · show a.2.2 = a.2.2 + _
        rw [if_neg (by omega : ¬ ((P.t1 c : Nat) < 0 ∧ _)), add_zero]
  | (k + 1), hk, a => by
      have hk' : k ≤ m := by omega
      have hkm : k < m := by omega
      show (growthSchedule data P).layerMap (k : ZMod m) (ι c)
          ((growthSchedule data P).prefixMap (ι c) k a) = _
      rw [growth_prefix_ι c k hk' a, growth_layerMap_ι]
      dsimp only
      refine Prod.ext rfl (Prod.ext ?_ ?_)
      · -- z₀ component
        show (a.2.1 + _) + _ = a.2.1 + _
        rw [if_congr (hits0_iff data P c hkm
          ((RootFlatCycle.schedule data.dir).prefixMap c k a.1)) rfl rfl]
        set q0 := (RootFlatCycle.schedule data.dir).prefixMap c (P.t0 c) a.1
          with hq0
        set qk := (RootFlatCycle.schedule data.dir).prefixMap c k a.1
          with hqk
        by_cases h1 : (P.t0 c : Nat) = k
        · have hpre : qk = q0 := by
            rw [hq0, hqk, h1]
          rw [if_neg (show ¬ ((P.t0 c : Nat) < k ∧ q0 = P.x0 c) from
            fun h => by omega), add_zero, hpre]
          by_cases hhit : q0 = P.x0 c
          · rw [if_pos ⟨h1, hhit⟩,
              if_pos (show (P.t0 c : Nat) < k + 1 ∧ q0 = P.x0 c from
                ⟨by omega, hhit⟩)]
          · rw [if_neg (show ¬ ((P.t0 c : Nat) = k ∧ q0 = P.x0 c) from
                fun h => hhit h.2),
              if_neg (show ¬ ((P.t0 c : Nat) < k + 1 ∧ q0 = P.x0 c) from
                fun h => hhit h.2),
              add_zero]
        · rw [if_neg (show ¬ ((P.t0 c : Nat) = k ∧ qk = P.x0 c) from
            fun h => h1 h.1), add_zero]
          by_cases h2 : (P.t0 c : Nat) < k ∧ q0 = P.x0 c
          · rw [if_pos h2,
              if_pos (show (P.t0 c : Nat) < k + 1 ∧ q0 = P.x0 c from
                ⟨by omega, h2.2⟩)]
          · rw [if_neg h2, add_zero,
              if_neg (show ¬ ((P.t0 c : Nat) < k + 1 ∧ q0 = P.x0 c) from
                fun h => h2 ⟨by omega, h.2⟩), add_zero]
      · -- z₁ component
        show (a.2.2 + _) + _ = a.2.2 + _
        rw [if_congr (hits1_iff data P c hkm
          ((RootFlatCycle.schedule data.dir).prefixMap c k a.1) _) rfl rfl]
        set q1 := (RootFlatCycle.schedule data.dir).prefixMap c (P.t1 c) a.1
          with hq1
        set qk := (RootFlatCycle.schedule data.dir).prefixMap c k a.1
          with hqk
        set q0 := (RootFlatCycle.schedule data.dir).prefixMap c (P.t0 c) a.1
          with hq0
        by_cases h1 : (P.t1 c : Nat) = k
        · have hord := P.order c
          have hnot0 : ¬ ((P.t0 c : Nat) < k ∧ q0 = P.x0 c) := by
            intro h
            omega
          have hpre : qk = q1 := by
            rw [hq1, hqk, h1]
          rw [if_neg (show ¬ ((P.t1 c : Nat) < k ∧ q1 = P.x1 c ∧
              a.2.1 = P.pin c) from fun h => by omega), add_zero,
            hpre, if_neg hnot0, add_zero]
          by_cases hhit : q1 = P.x1 c ∧ a.2.1 = P.pin c
          · rw [if_pos (show (P.t1 c : Nat) = k ∧ q1 = P.x1 c ∧
                a.2.1 = P.pin c from ⟨h1, hhit.1, hhit.2⟩),
              if_pos (show (P.t1 c : Nat) < k + 1 ∧ q1 = P.x1 c ∧
                a.2.1 = P.pin c from ⟨by omega, hhit.1, hhit.2⟩)]
          · rw [if_neg (show ¬ ((P.t1 c : Nat) = k ∧ q1 = P.x1 c ∧
                a.2.1 = P.pin c) from fun h => hhit ⟨h.2.1, h.2.2⟩),
              if_neg (show ¬ ((P.t1 c : Nat) < k + 1 ∧ q1 = P.x1 c ∧
                a.2.1 = P.pin c) from fun h => hhit ⟨h.2.1, h.2.2⟩),
              add_zero]
        · rw [if_neg (show ¬ ((P.t1 c : Nat) = k ∧ qk = P.x1 c ∧
            (a.2.1 + if (P.t0 c : Nat) < k ∧ q0 = P.x0 c then 1 else 0)
              = P.pin c) from fun h => h1 h.1), add_zero]
          by_cases h2 : (P.t1 c : Nat) < k ∧ q1 = P.x1 c ∧ a.2.1 = P.pin c
          · rw [if_pos h2,
              if_pos (show (P.t1 c : Nat) < k + 1 ∧ q1 = P.x1 c ∧
                a.2.1 = P.pin c from ⟨by omega, h2.2⟩)]
          · rw [if_neg h2, add_zero,
              if_neg (show ¬ ((P.t1 c : Nat) < k + 1 ∧ q1 = P.x1 c ∧
                a.2.1 = P.pin c) from fun h => h2 ⟨by omega, h.2⟩),
              add_zero]

/-- `z₀`-carry of an old color: `1` exactly when the old orbit stands on the
crossing plane at its layer. -/
noncomputable def carry0 (c : Fin (n + 1)) (x : RootState n m) : ZMod m :=
  if (RootFlatCycle.schedule data.dir).prefixMap c (P.t0 c) x = P.x0 c
  then 1 else 0

/-- `z₁`-carry of an old color: `1` exactly on the pinned crossing line. -/
noncomputable def carry1 (c : Fin (n + 1)) (x : RootState n m)
    (z₀ : ZMod m) : ZMod m :=
  if (RootFlatCycle.schedule data.dir).prefixMap c (P.t1 c) x = P.x1 c ∧
      z₀ = P.pin c then 1 else 0

/-- **The return decomposition for old colors** (the G4 per-color shape,
validated pointwise by the numeric gate). -/
theorem growth_return_ι (c : Fin (n + 1)) (a : GrowState n m) :
    (growthSchedule data P).returnMap (ι c) a =
      ((RootFlatCycle.schedule data.dir).returnMap c a.1,
       a.2.1 + carry0 data P c a.1,
       a.2.2 + carry1 data P c a.1 a.2.1) := by
  rw [Shared.RootFlatSchedule.returnMap_eq_prefixMap,
    Shared.RootFlatSchedule.returnMap_eq_prefixMap,
    growth_prefix_ι data P c m le_rfl a]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · show a.2.1 + _ = a.2.1 + carry0 data P c a.1
    rw [carry0, if_congr (and_iff_right (P.t0 c).isLt) rfl rfl]
  · show a.2.2 + _ = a.2.2 + carry1 data P c a.1 a.2.1
    rw [carry1, if_congr (and_iff_right (P.t1 c).isLt) rfl rfl]

end Schedule

section Single

variable (data : RootFlatCycleData n m) (P : GrowthPlacement n m data.dir)

omit [NeZero m] in
theorem sum_indicator_bij {X : Type*} [Fintype X] [DecidableEq X]
    {f : X → X} (hf : Function.Bijective f) (y : X) :
    (∑ x : X, if f x = y then (1 : ZMod m) else 0) = 1 := by
  classical
  rw [Fintype.sum_bijective f hf _
    (fun x' => if x' = y then (1 : ZMod m) else 0) (fun x => rfl)]
  simp

/-- **RF3 for old colors**: the decomposed return is a double `pointCarry`
tower over the old return's rank — a single `K·m²`-cycle. -/
theorem growth_return_ι_singleCycle (c : Fin (n + 1)) :
    Shared.IsSingleCycleMap ((growthSchedule data P).returnMap (ι c)) := by
  classical
  haveI hne : Nonempty (RootState n m) := ⟨fun _ => 0⟩
  haveI : NeZero (Nat.card (RootState n m)) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨rank, hrank⟩ := CompletionTower.rankEquiv_of_singleCycle
    ((RootFlatCycle.schedule data.dir).returnMap c)
    (data.returnsSingleCycle c) rfl
  have hsum0 : (∑ x : RootState n m, carry0 data P c x) = 1 := by
    simp only [carry0]
    exact sum_indicator_bij
      (Shared.RootFlatSchedule.prefixMap_bijective _
        data.layerBijective c (P.t0 c)) (P.x0 c)
  have hinner : Shared.IsSingleCycleMap
      (additiveSkewMap ((RootFlatCycle.schedule data.dir).returnMap c)
        (carry0 data P c)) :=
    rankUnitCarrySingleCycle _ rank (carry0 data P c) (fun _ => 0) hrank
      (by rw [hsum0]; exact isUnit_one)
  haveI : NeZero (Nat.card (RootState n m × ZMod m)) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨rank2, hrank2⟩ := CompletionTower.rankEquiv_of_singleCycle _
    hinner rfl
  have hbijF : Function.Bijective (fun p : RootState n m × ZMod m =>
      ((RootFlatCycle.schedule data.dir).prefixMap c (P.t1 c) p.1, p.2)) :=
    (Shared.RootFlatSchedule.prefixMap_bijective _
      data.layerBijective c (P.t1 c)).prodMap Function.bijective_id
  have hsum1 : (∑ p : RootState n m × ZMod m,
      carry1 data P c p.1 p.2) = 1 := by
    rw [← sum_indicator_bij (m := m) hbijF (P.x1 c, P.pin c)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [carry1]
    exact if_congr
      ⟨fun h => Prod.ext h.1 h.2,
        fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩ rfl rfl
  have houter : Shared.IsSingleCycleMap
      (additiveSkewMap
        (additiveSkewMap ((RootFlatCycle.schedule data.dir).returnMap c)
          (carry0 data P c))
        (fun p => carry1 data P c p.1 p.2)) :=
    rankUnitCarrySingleCycle _ rank2 _ ((fun _ => 0), 0) hrank2
      (by rw [hsum1]; exact isUnit_one)
  refine Shared.single_cycle_of_equiv_conj
    (Equiv.prodAssoc (RootState n m) (ZMod m) (ZMod m))
    ((growthSchedule data P).returnMap (ι c)) _ houter ?_
  rintro ⟨⟨x, z₀⟩, z₁⟩
  show (Equiv.prodAssoc _ _ _).symm
      ((growthSchedule data P).returnMap (ι c) (x, z₀, z₁)) = _
  rw [growth_return_ι data P c (x, z₀, z₁)]
  rfl

end Single

/-! ## Part 4: transport to the grown root state and the realization

`growthDir` is the constructed child schedule on `RootState (n+2) m`.
Its RF1/RF2 and the old-color RF3 are CLOSED; the two new colors are the
precisely shaped remaining obligation (`GrowthRealization`): any child
schedule agreeing with `growthDir` on the old-color returns and adding
single-cycle new-color returns realizes the full child cycle data. -/

section Transport

variable (data : RootFlatCycleData n m) (P : GrowthPlacement n m data.dir)

/-- The constructed child `dir` on the grown root state. -/
noncomputable def growthDir : ZMod m → RootState (n + 2) m →
    Shared.TorusColor (n + 3) → Shared.TorusDirection (n + 3) :=
  HEDBaseWitnesses.transportDir (growthSchedule data P) growEquiv

/-- **RF1 for the realized child schedule.** -/
theorem growthDir_rowLatin :
    (RootFlatCycle.schedule (growthDir data P)).rowLatin := by
  intro t w
  exact growthSchedule_rowLatin data P t (growEquiv.symm w)

/-- **RF2 for the realized child schedule.** -/
theorem growthDir_layerBijective :
    (RootFlatCycle.schedule (growthDir data P)).layerBijective :=
  HEDBaseWitnesses.transport_layerBijective (growthSchedule data P) growEquiv
    growStep_conj (growthSchedule_layerBijective data P)

/-- **RF3 at every old color of the realized child schedule** (closed). -/
theorem growthDir_return_ι_singleCycle (c : Fin (n + 1)) :
    Shared.IsSingleCycleMap
      ((RootFlatCycle.schedule (growthDir data P)).returnMap (ι c)) := by
  refine Shared.single_cycle_of_equiv_conj growEquiv _ _
    (growth_return_ι_singleCycle data P c) ?_
  intro a
  apply growEquiv.injective
  rw [Equiv.apply_symm_apply]
  simp only [growthDir]
  rw [HEDBaseWitnesses.transport_returnMap_conj (growthSchedule data P)
    growEquiv growStep_conj (ι c) a]

/-- The realized child return at an embedded point, in closed form (the
selector/reserve transports consume this). -/
theorem growthDir_return_ι_embed (c : Fin (n + 1)) (x : RootState n m)
    (z₀ z₁ : ZMod m) :
    (RootFlatCycle.schedule (growthDir data P)).returnMap (ι c)
        (embedSt x z₀ z₁) =
      embedSt ((RootFlatCycle.schedule data.dir).returnMap c x)
        (z₀ + carry0 data P c x) (z₁ + carry1 data P c x z₀) := by
  have h := HEDBaseWitnesses.transport_returnMap_conj (growthSchedule data P)
    growEquiv growStep_conj (ι c) ((x, z₀, z₁) : GrowState n m)
  rw [show embedSt x z₀ z₁ = growEquiv ((x, z₀, z₁) : GrowState n m) from rfl]
  simp only [growthDir]
  rw [h, growth_return_ι]
  rfl

end Transport

/-- **The shaped remaining obligation (the open core)**: a child schedule
`dir⋆` that keeps the constructed old-color returns and realizes the two
new-color returns as single cycles.  Every field except the two
`newReturn` fields is satisfied by `growthDir` itself; the numeric gate
(`--core-findings`) documents why the new colors need a genuinely richer
row structure over a black-box input. -/
structure GrowthRealization (data : RootFlatCycleData n m)
    (P : GrowthPlacement n m data.dir) : Type where
  /-- the realized child schedule. -/
  dir : ZMod m → RootState (n + 2) m →
    Shared.TorusColor (n + 3) → Shared.TorusDirection (n + 3)
  /-- RF1 of the realized schedule. -/
  rowLatin : (RootFlatCycle.schedule dir).rowLatin
  /-- RF2 of the realized schedule. -/
  layerBijective : (RootFlatCycle.schedule dir).layerBijective
  /-- the old-color returns agree with the constructed schedule (so the
  closed decomposition and its single-cyclicity apply verbatim). -/
  oldReturns_eq : ∀ c : Fin (n + 1),
    (RootFlatCycle.schedule dir).returnMap (ι c) =
      (RootFlatCycle.schedule (growthDir data P)).returnMap (ι c)
  /-- RF3 at the first new color. -/
  newReturn0 : Shared.IsSingleCycleMap
    ((RootFlatCycle.schedule dir).returnMap leaf0)
  /-- RF3 at the second new color. -/
  newReturn1 : Shared.IsSingleCycleMap
    ((RootFlatCycle.schedule dir).returnMap leaf1)

/-- The realized child cycle data: RF1/RF2 from the realization, RF3 for old
colors CLOSED by the return decomposition, new colors from the realization
fields. -/
noncomputable def GrowthRealization.cycleData
    {data : RootFlatCycleData n m} {P : GrowthPlacement n m data.dir}
    (R : GrowthRealization data P) : RootFlatCycleData (n + 2) m where
  dir := R.dir
  rowLatin := R.rowLatin
  layerBijective := R.layerBijective
  returnsSingleCycle := by
    intro c'
    rcases color_cases c' with ⟨c, rfl⟩ | rfl | rfl
    · rw [R.oldReturns_eq c]
      exact growthDir_return_ι_singleCycle data P c
    · exact R.newReturn0
    · exact R.newReturn1

/-! ## Part 5: the output chain fields (`lem:chain-output-assembly`)

The next step's interface is the ORDINARY paired window in the output chart
`ZMod (n+5)` (`GuideLocality`'s audited tables, phases `ρ = 3, 7`), with new
labels `(0, 3)`, the old labels re-embedded off `{0, 3}`, and the terminal
carrier on `{5, 6, 7}` — disjoint from both row supports for `n ≥ 6`. -/

section Chain

omit [NeZero m]

theorem zmod_natCast_ne {N a b : Nat} (ha : a < N) (hb : b < N)
    (hab : a ≠ b) : ((a : Nat) : ZMod N) ≠ ((b : Nat) : ZMod N) := by
  intro h
  exact hab (Nat.ModEq.eq_of_lt_of_lt
    ((ZMod.natCast_eq_natCast_iff a b N).mp h) ha hb)

theorem zmod_neg_one_cast {N : Nat} (h1 : 1 ≤ N) :
    (-1 : ZMod N) = ((N - 1 : Nat) : ZMod N) := by
  rw [Nat.cast_sub h1, ZMod.natCast_self, Nat.cast_one, zero_sub]

theorem zmod_neg_two_cast {N : Nat} (h2 : 2 ≤ N) :
    (-2 : ZMod N) = ((N - 2 : Nat) : ZMod N) := by
  rw [Nat.cast_sub h2, ZMod.natCast_self, zero_sub]
  norm_num

/-- Old labels of the output chart: `0 ↦ 1`, `1 ↦ 2`, `i ↦ i + 2` —
injective and avoiding the new labels `{0, 3}`. -/
def nextOldLabel (i : Fin (n + 3)) : ZMod (n + 5) :=
  if (i : Nat) = 0 then ((1 : Nat) : ZMod (n + 5))
  else if (i : Nat) = 1 then ((2 : Nat) : ZMod (n + 5))
  else (((i : Nat) + 2 : Nat) : ZMod (n + 5))

/-- The `Nat` value carried by `nextOldLabel`. -/
def nextOldLabelNat (i : Fin (n + 3)) : Nat :=
  if (i : Nat) = 0 then 1 else if (i : Nat) = 1 then 2 else (i : Nat) + 2

theorem nextOldLabel_eq_cast (i : Fin (n + 3)) :
    nextOldLabel i = ((nextOldLabelNat i : Nat) : ZMod (n + 5)) := by
  rw [nextOldLabel, nextOldLabelNat]
  by_cases h0 : (i : Nat) = 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : (i : Nat) = 1
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1]

theorem nextOldLabelNat_lt (i : Fin (n + 3)) :
    nextOldLabelNat i < n + 5 := by
  have := i.isLt
  rw [nextOldLabelNat]
  by_cases h0 : (i : Nat) = 0
  · rw [if_pos h0]; omega
  · rw [if_neg h0]
    by_cases h1 : (i : Nat) = 1
    · rw [if_pos h1]; omega
    · rw [if_neg h1]; omega

theorem nextOldLabelNat_mk (a : Nat) (h : a < n + 3) (h2 : 2 ≤ a) :
    nextOldLabelNat (⟨a, h⟩ : Fin (n + 3)) = a + 2 := by
  rw [nextOldLabelNat,
    if_neg (show ¬ ((⟨a, h⟩ : Fin (n + 3)) : Nat) = 0 from by
      show ¬ a = 0
      omega),
    if_neg (show ¬ ((⟨a, h⟩ : Fin (n + 3)) : Nat) = 1 from by
      show ¬ a = 1
      omega)]

theorem nextOldLabelNat_injective :
    Function.Injective (nextOldLabelNat (n := n)) := by
  intro a b hab
  have ha := a.isLt
  have hb := b.isLt
  rw [nextOldLabelNat, nextOldLabelNat] at hab
  apply Fin.ext
  split_ifs at hab <;> omega

theorem nextOldLabel_injective :
    Function.Injective (nextOldLabel (n := n)) := by
  intro a b hab
  rw [nextOldLabel_eq_cast, nextOldLabel_eq_cast] at hab
  refine nextOldLabelNat_injective ?_
  by_contra hne
  exact zmod_natCast_ne (nextOldLabelNat_lt a) (nextOldLabelNat_lt b) hne hab

/-- The next growth rows: `GuideLocality`'s ordinary paired tables in the
output chart, at the certified boundary-avoiding phases `ρ = 3, 7`. -/
def nextRow (r : GuideLocality.OrdinaryHighEvenRow) :
    HEDWitness.GrowthRowInterface (n + 2) where
  support := GuideLocality.ordinaryHighEvenRowSupport r
  leafLine := GuideLocality.ordinaryHighEvenRowLeafLine r
  quotientGen := GuideLocality.ordinaryHighEvenRowQuotientGenerator r
  oldGens := GuideLocality.ordinaryHighEvenRowNonzeroPairs r
  phase := GuideLocality.ordinaryHighEvenBoundaryAvoidingPhaseChoice r
  delta := GuideLocality.ordinaryHighEvenRowDelta r

/-- Carrier labels `{5, 6, 7}` of the output chart. -/
def nextCarrier (j : Fin 3) : ZMod (n + 5) :=
  (((j : Nat) + 5 : Nat) : ZMod (n + 5))

theorem mem_support_cast (hn : 6 ≤ n) (a : Nat) (ha : 5 ≤ a) (ha7 : a ≤ 7)
    (r : GuideLocality.OrdinaryHighEvenRow) :
    ((a : Nat) : ZMod (n + 5)) ∉
      GuideLocality.ordinaryHighEvenRowSupport (D := n + 5) r := by
  intro hmem
  have hcast : ∀ b : Nat, b < n + 5 → a ≠ b →
      ¬ (((a : Nat) : ZMod (n + 5)) = ((b : Nat) : ZMod (n + 5))) :=
    fun b hb hab => zmod_natCast_ne (by omega) hb hab
  cases r <;>
    simp only [GuideLocality.ordinaryHighEvenRowSupport, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
  · rcases hmem with h | h | h | h
    · exact hcast 0 (by omega) (by omega) (by rw [h]; norm_num)
    · exact hcast 1 (by omega) (by omega) (by rw [h]; norm_num)
    · refine hcast (n + 4) (by omega) (by omega) ?_
      rw [h, zmod_neg_one_cast (by omega : 1 ≤ n + 5)]
      congr 1
    · refine hcast (n + 3) (by omega) (by omega) ?_
      rw [h, zmod_neg_two_cast (by omega : 2 ≤ n + 5)]
      congr 1
  · rcases hmem with h | h | h | h
    · exact hcast 3 (by omega) (by omega) (by rw [h]; norm_num)
    · exact hcast 4 (by omega) (by omega) (by rw [h]; norm_num)
    · exact hcast 2 (by omega) (by omega) (by rw [h]; norm_num)
    · exact hcast 1 (by omega) (by omega) (by rw [h]; norm_num)

/-- The output chain fields (`def:high-even-chain-datum` items 2–5 for the
NEXT step). -/
def nextChainFields (hn : 6 ≤ n) : HEDWitness.ChainFields (n + 2) where
  newLabels := (0, ((3 : Nat) : ZMod (n + 5)))
  oldLabel := nextOldLabel
  rows := fun r =>
    nextRow (if r = 0 then GuideLocality.OrdinaryHighEvenRow.first
      else GuideLocality.OrdinaryHighEvenRow.second)
  carrier := nextCarrier
  newLabels_ne := by
    have : ((0 : Nat) : ZMod (n + 5)) ≠ ((3 : Nat) : ZMod (n + 5)) :=
      zmod_natCast_ne (by omega) (by omega) (by omega)
    simpa using this
  oldLabel_inj := nextOldLabel_injective
  oldLabel_avoids_new := by
    intro i
    rw [nextOldLabel_eq_cast]
    have hlt := nextOldLabelNat_lt i
    have hne0 : nextOldLabelNat i ≠ 0 := by
      rw [nextOldLabelNat]
      by_cases h0 : (i : Nat) = 0
      · rw [if_pos h0]; omega
      · rw [if_neg h0]
        by_cases h1 : (i : Nat) = 1
        · rw [if_pos h1]; omega
        · rw [if_neg h1]; omega
    have hne3 : nextOldLabelNat i ≠ 3 := by
      rw [nextOldLabelNat]
      by_cases h0 : (i : Nat) = 0
      · rw [if_pos h0]; omega
      · rw [if_neg h0]
        by_cases h1 : (i : Nat) = 1
        · rw [if_pos h1]; omega
        · rw [if_neg h1]
          have := i.isLt
          omega
    constructor
    · have := zmod_natCast_ne (N := n + 5) hlt (by omega) hne0
      simpa using this
    · exact zmod_natCast_ne hlt (by omega) hne3
  carrier_inj := by
    intro a b hab
    have ha := a.isLt
    have hb := b.isLt
    rw [nextCarrier, nextCarrier] at hab
    apply Fin.ext
    by_contra hne
    exact zmod_natCast_ne (by omega) (by omega) (by omega) hab
  carrier_on_old := by
    intro j
    have hj := j.isLt
    refine ⟨⟨(j : Nat) + 3, by omega⟩, ?_⟩
    rw [nextCarrier, nextOldLabel_eq_cast,
      nextOldLabelNat_mk ((j : Nat) + 3) (by omega) (by omega)]
  carrier_avoids_supports := by
    intro j r
    have hj := j.isLt
    rw [nextCarrier]
    exact mem_support_cast hn ((j : Nat) + 5) (by omega) (by omega) _

end Chain

/-! ## Part 6: witness transport and the assembled growth step

Selector transport at the leaf pins `(2, 2)`; reserve transport `n+4 → n+6`
with the two renewal sites at leaf value `3` in the leaf fibers of the
reserve head; growth traces at leaf values `{0, 1}`
(`lem:growth-leaf-fiber-room`: `0,1,2,3` distinct since `4 ≤ m`). -/

section Witness

variable (W : HEDWitness.HEDWitness n m)

/-- Leaf-fiber values as `ZMod m` (trace `0,1`, transported reserve `2`,
renewal `3`). -/
def zv (a : Nat) : ZMod m := ((a : Nat) : ZMod m)

/-- Placement over a witness, with the selector-avoidance clauses that make
the marked closure clauses transport. -/
structure WitnessPlacement (W : HEDWitness.HEDWitness n m) : Type where
  /-- the crossing placement over the witness schedule. -/
  place : GrowthPlacement n m W.cycleData.dir
  /-- the first marked color's plane crossing misses the selector orbit. -/
  selAvoid0_first :
    (RootFlatCycle.schedule W.cycleData.dir).prefixMap W.selector.firstColor
      (place.t0 W.selector.firstColor) W.selector.point ≠
      place.x0 W.selector.firstColor
  /-- the second marked color's plane crossing misses the selector orbit. -/
  selAvoid0_second :
    (RootFlatCycle.schedule W.cycleData.dir).prefixMap W.selector.secondColor
      (place.t0 W.selector.secondColor) W.selector.point ≠
      place.x0 W.selector.secondColor
  /-- the first marked color's line crossing misses the pinned selector. -/
  selAvoid1_first :
    ¬ ((RootFlatCycle.schedule W.cycleData.dir).prefixMap
        W.selector.firstColor (place.t1 W.selector.firstColor)
        W.selector.point = place.x1 W.selector.firstColor ∧
      zv (m := m) 2 = place.pin W.selector.firstColor)
  /-- the second marked color's line crossing misses the pinned selector. -/
  selAvoid1_second :
    ¬ ((RootFlatCycle.schedule W.cycleData.dir).prefixMap
        W.selector.secondColor (place.t1 W.selector.secondColor)
        W.selector.point = place.x1 W.selector.secondColor ∧
      zv (m := m) 2 = place.pin W.selector.secondColor)

/-- The transported marked selector (point and image pinned at `(2, 2)` in
the leaf fibers; closure clauses from the return decomposition plus the
avoidance clauses). -/
noncomputable def growSelector (WP : WitnessPlacement W)
    (R : GrowthRealization W.cycleData WP.place) :
    HEDWitness.MarkedSelector (n + 2) m R.cycleData.dir where
  firstColor := ι W.selector.firstColor
  secondColor := ι W.selector.secondColor
  point := embedSt W.selector.point (zv 2) (zv 2)
  commonImage := embedSt W.selector.commonImage (zv 2) (zv 2)
  protectedPoints :=
    W.selector.protectedPoints.map (fun p => embedSt p (zv 2) (zv 2))
  colors_ne := fun h => W.selector.colors_ne (ι_injective h)
  closure_first := by
    show (RootFlatCycle.schedule R.dir).returnMap (ι W.selector.firstColor)
        (embedSt W.selector.point (zv 2) (zv 2)) = _
    rw [R.oldReturns_eq, growthDir_return_ι_embed,
      show carry0 W.cycleData WP.place W.selector.firstColor
          W.selector.point = 0 from if_neg WP.selAvoid0_first,
      show carry1 W.cycleData WP.place W.selector.firstColor
          W.selector.point (zv 2) = 0 from if_neg WP.selAvoid1_first,
      add_zero, W.selector.closure_first]
  closure_second := by
    show (RootFlatCycle.schedule R.dir).returnMap (ι W.selector.secondColor)
        (embedSt W.selector.point (zv 2) (zv 2)) = _
    rw [R.oldReturns_eq, growthDir_return_ι_embed,
      show carry0 W.cycleData WP.place W.selector.secondColor
          W.selector.point = 0 from if_neg WP.selAvoid0_second,
      show carry1 W.cycleData WP.place W.selector.secondColor
          W.selector.point (zv 2) = 0 from if_neg WP.selAvoid1_second,
      add_zero, W.selector.closure_second]
  card_unit := isUnit_one
  postSwitch_first := R.cycleData.returnsSingleCycle (ι W.selector.firstColor)
  postSwitch_second :=
    R.cycleData.returnsSingleCycle (ι W.selector.secondColor)
  point_mem_protected :=
    List.mem_map_of_mem W.selector.point_mem_protected
  image_mem_protected :=
    List.mem_map_of_mem W.selector.image_mem_protected
  protected_nodup :=
    W.selector.protected_nodup.map
      (fun a b h => (embedSt_injective2 h).1)

/-- The first incoming reserve site (the head of the fixed-fiber list). -/
noncomputable def reserveHead : RootState n m :=
  W.reserve.sites.head (List.ne_nil_of_length_pos (by
    rw [W.reserve.count]; omega))

theorem reserveHead_mem : reserveHead W ∈ W.reserve.sites :=
  List.head_mem _

/-- The transported reserve sites: the incoming sites at leaf pins `(2, 2)`
plus the two renewal sites at leaf value `3` in the head fiber. -/
noncomputable def growReserveSites : List (RootState (n + 2) m) :=
  W.reserve.sites.map (fun p => embedSt p (zv 2) (zv 2)) ++
    [embedSt (reserveHead W) (zv 3) (zv 2),
     embedSt (reserveHead W) (zv 2) (zv 3)]

/-- The free coordinates of the transported reserve: the incoming free
coordinates plus the two leaf coordinates. -/
def growReserveFree (free : List (Fin n)) : List (Fin (n + 2)) :=
  free.map (Fin.castLE (by omega)) ++ [⟨n, by omega⟩, ⟨n + 1, by omega⟩]

/-- Every transported site is an embedded incoming site with leaf values
among `{(2,2), (3,2), (2,3)}`. -/
theorem growReserveSites_form {q : RootState (n + 2) m}
    (hq : q ∈ growReserveSites W) :
    ∃ s ∈ W.reserve.sites, ∃ a b : Nat,
      (a = 2 ∨ a = 3) ∧ (b = 2 ∨ b = 3) ∧ q = embedSt s (zv a) (zv b) := by
  rcases List.mem_append.mp hq with h | h
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
    exact ⟨s, hs, 2, 2, Or.inl rfl, Or.inl rfl, rfl⟩
  · rcases List.mem_cons.mp h with rfl | h
    · exact ⟨reserveHead W, reserveHead_mem W, 3, 2, Or.inr rfl,
        Or.inl rfl, rfl⟩
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨reserveHead W, reserveHead_mem W, 2, 3, Or.inl rfl,
          Or.inr rfl, rfl⟩
      · exact absurd h (List.not_mem_nil)

/-- A pinned coordinate of the transported reserve below `n` comes from a
pinned incoming coordinate. -/
theorem growReserveFree_lt {free : List (Fin n)} {i : Fin (n + 2)}
    (hi : i ∉ growReserveFree (n := n) free) :
    ∃ h : (i : Nat) < n, (⟨(i : Nat), h⟩ : Fin n) ∉ free := by
  have hlt : (i : Nat) < n := by
    by_contra h
    have := i.isLt
    apply hi
    rw [growReserveFree]
    refine List.mem_append.mpr (Or.inr ?_)
    by_cases hn0 : (i : Nat) = n
    · exact List.mem_cons.mpr (Or.inl (Fin.ext hn0))
    · refine List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl ?_)))
      exact Fin.ext (show (i : Nat) = n + 1 by omega)
  refine ⟨hlt, fun hmem => hi ?_⟩
  rw [growReserveFree]
  refine List.mem_append.mpr (Or.inl ?_)
  refine List.mem_map.mpr ⟨⟨(i : Nat), hlt⟩, hmem, ?_⟩
  exact Fin.ext rfl

/-- The transported reserve (`lem:growth-reserve-transport`). -/
noncomputable def growReserve (hm : 4 ≤ m) :
    HEDWitness.ReserveSites (n + 2) m where
  sites := growReserveSites W
  freeCoords := growReserveFree W.reserve.freeCoords
  count := by
    rw [growReserveSites, List.length_append, List.length_map,
      W.reserve.count]
    rfl
  nodup := by
    rw [growReserveSites, List.nodup_append]
    refine ⟨W.reserve.nodup.map (fun a b h => (embedSt_injective2 h).1),
      ?_, ?_⟩
    · refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
      intro hmem
      rcases List.mem_singleton.mp hmem with h
      have := (embedSt_injective2 h).2.1
      exact zmod_natCast_ne (a := 3) (b := 2) (by omega) (by omega)
        (by omega) this
    · intro q hq q2 hq2
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp hq
      intro heq
      rcases List.mem_cons.mp hq2 with h | h
      · exact zmod_natCast_ne (a := 2) (b := 3) (by omega) (by omega)
          (by omega) ((embedSt_injective2 (heq.trans h)).2.1)
      · rcases List.mem_cons.mp h with h | h
        · exact zmod_natCast_ne (a := 2) (b := 3) (by omega) (by omega)
            (by omega) ((embedSt_injective2 (heq.trans h)).2.2)
        · exact absurd h (List.not_mem_nil)
  fixedFiber := by
    intro p hp q hq i hi
    obtain ⟨hlt, hfree⟩ := growReserveFree_lt hi
    obtain ⟨s, hs, a, b, -, -, rfl⟩ := growReserveSites_form W hp
    obtain ⟨s', hs', a', b', -, -, rfl⟩ := growReserveSites_form W hq
    rw [embedSt_apply_lt _ _ _ (i := ⟨(i : Nat), hlt⟩) rfl,
      embedSt_apply_lt _ _ _ (i := ⟨(i : Nat), hlt⟩) rfl]
    exact W.reserve.fixedFiber s hs s' hs' _ hfree

end Witness

section Assembly

variable (W : HEDWitness.HEDWitness n m)

/-- The transported switching ledger: incoming traces at leaf values
`(0, 0)` plus the growth crossing traces at leaf values `(1, 1)`. -/
noncomputable def growTraces (WP : WitnessPlacement W) :
    List (RootState (n + 2) m) :=
  W.usedTraces.map (fun p => embedSt p (zv 0) (zv 0)) ++
    ((List.finRange (n + 1)).map
        (fun c => embedSt (WP.place.x0 c) (zv 1) (zv 1)) ++
      (List.finRange (n + 1)).map
        (fun c => embedSt (WP.place.x1 c) (zv 1) (zv 1)))

theorem castLE_not_mem_growReserveFree {free : List (Fin n)} {j : Fin n}
    (hj : j ∉ free) :
    (Fin.castLE (by omega) j : Fin (n + 2)) ∉ growReserveFree free := by
  intro hmem
  rcases List.mem_append.mp hmem with h | h
  · obtain ⟨j', hj', heq⟩ := List.mem_map.mp h
    exact hj (by
      have : j' = j := Fin.castLE_injective _ heq
      rwa [this] at hj')
  · have hval : ((Fin.castLE (by omega) j : Fin (n + 2)) : Nat) = (j : Nat) :=
      rfl
    have hjlt := j.isLt
    rcases List.mem_cons.mp h with h1 | h1
    · have hv : (j : Nat) = n := congrArg Fin.val h1
      omega
    · rcases List.mem_cons.mp h1 with h2 | h2
      · have hv : (j : Nat) = n + 1 := congrArg Fin.val h2
        omega
      · exact absurd h2 (List.not_mem_nil)

/-- **The transported witness** — the realized child cycle data plus all
transported witness-level fields. -/
noncomputable def growWitness (hn : 6 ≤ n) (hm : 4 ≤ m)
    (WP : WitnessPlacement W)
    (R : GrowthRealization W.cycleData WP.place) :
    HEDWitness.HEDWitness (n + 2) m where
  cycleData := R.cycleData
  selector := growSelector W WP R
  reserve := growReserve W hm
  usedTraces := growTraces W WP
  chain := nextChainFields hn
  reserveSeparated := by
    intro p hp q hq
    obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
    obtain ⟨s, hs, a, b, -, -, rfl⟩ := growReserveSites_form W hq
    obtain ⟨j, hjfree, hjne⟩ := W.reserveSeparated p₀ hp₀ s hs
    refine ⟨Fin.castLE (by omega) j,
      castLE_not_mem_growReserveFree hjfree, ?_⟩
    rw [embedSt_apply_lt _ _ _ (i := j) rfl,
      embedSt_apply_lt _ _ _ (i := j) rfl]
    exact hjne
  reserveAvoidsTraces := by
    intro q hq hmem
    obtain ⟨s, hs, a, b, ha, hb, rfl⟩ := growReserveSites_form W hq
    have hane : ∀ a' : Nat, a' < 2 → zv (m := m) a ≠ zv a' := by
      intro a' ha' heq
      rcases ha with rfl | rfl <;>
        exact zmod_natCast_ne (by omega) (by omega) (by omega) heq
    rcases List.mem_append.mp hmem with h | h
    · obtain ⟨t, -, heq⟩ := List.mem_map.mp h
      exact hane 0 (by omega) (embedSt_injective2 heq.symm).2.1
    · rcases List.mem_append.mp h with h1 | h1
      · obtain ⟨c, -, heq⟩ := List.mem_map.mp h1
        exact hane 1 (by omega) (embedSt_injective2 heq.symm).2.1
      · obtain ⟨c, -, heq⟩ := List.mem_map.mp h1
        exact hane 1 (by omega) (embedSt_injective2 heq.symm).2.1

end Assembly

/-! ## Part 7: the assembled growth step

`GrowthStepHypotheses` is the COMPLETE bundle of per-step obligations of
this module: the dimension/modulus bounds, a crossing placement with
selector avoidance for every input witness, and the new-color realization
(`GrowthRealization`).  Everything else — RF1, RF2, old-color RF3 with the
per-color decomposition, selector/reserve/trace/chain transports — is
closed above.  Producing these hypotheses (in particular the two new-color
single-cycle returns) is the remaining G4 obligation; the numeric gate
documents its exact difficulty over the dimension-7 blobs. -/

/-- The shaped per-step hypotheses (everything G4 still owes). -/
structure GrowthStepHypotheses (n m : Nat) [NeZero m] : Type where
  /-- root dimension bound (`n = 2k ≥ 6`). -/
  hn : 6 ≤ n
  /-- modulus bound (leaf-fiber room, `lem:growth-leaf-fiber-room`). -/
  hm : 4 ≤ m
  /-- a crossing placement with selector avoidance, per input witness. -/
  placement : (W : HEDWitness.HEDWitness n m) → WitnessPlacement W
  /-- the new-color realization, per input witness (the open core). -/
  realization : (W : HEDWitness.HEDWitness n m) →
    GrowthRealization W.cycleData (placement W).place

/-- **The growth step** (G4): closed core + shaped hypotheses
(`prop:chained-two-hole` / `prop:paired-growth` at witness granularity). -/
noncomputable def growthStep (H : GrowthStepHypotheses n m) :
    HEDWitness.GrowthStep n m where
  apply W := growWitness W H.hn H.hm (H.placement W) (H.realization W)

/-- Driver wiring (G5 shape): step hypotheses at every even root dimension
discharge the chain-propagation driver from the dimension-7 bases. -/
example {m : Nat} [NeZero m]
    (H : ∀ k, 3 ≤ k → GrowthStepHypotheses (2 * k) m)
    (base : HEDWitness.HEDWitness 6 m) :
    FinalMarkedTarget 9 m ∧ FinalMarkedTarget 11 m :=
  ⟨HEDWitness.propagate (fun k hk => growthStep (H k hk)) base 9
      (by omega) (by omega),
    HEDWitness.propagate (fun k hk => growthStep (H k hk)) base 11
      (by omega) (by omega)⟩

/-- The naive child schedule itself discharges every realization field
except the two new-color returns (the design-doc Part-1.3 finding made
formal: ONLY those two fields are open). -/
noncomputable def GrowthRealization.ofNewReturns
    (data : RootFlatCycleData n m) (P : GrowthPlacement n m data.dir)
    (h0 : Shared.IsSingleCycleMap
      ((RootFlatCycle.schedule (growthDir data P)).returnMap leaf0))
    (h1 : Shared.IsSingleCycleMap
      ((RootFlatCycle.schedule (growthDir data P)).returnMap leaf1)) :
    GrowthRealization data P where
  dir := growthDir data P
  rowLatin := growthDir_rowLatin data P
  layerBijective := growthDir_layerBijective data P
  oldReturns_eq := fun _ => rfl
  newReturn0 := h0
  newReturn1 := h1

end GrowthStepCore
end V28Hard
end EvenV11
