import EvenV11.V28Hard.EndpointRowSchedule
import EvenV11.ProjectionKernel

/-!
# Growth slot G1: multi-substitution row layers (multi-swap RF2)

Extends the E5 row-schedule RF2 machinery of
`EvenV11.V28Hard.EndpointRowSchedule` from single swap-on-cylinder layers to
the multi-substitution layers the growth/anchor constructions need
(`docs/GROWTH_ENGINE_DESIGN_20260610.md`, module G1; paper growth rows
`σ_{s,δ} = (s a)(b c)` and the anchor rank-countdown splice units).

A *multi-swap layer* substitutes a family of transpositions
`(α_i β_i)` over a base permutation `ρ`, each on its own support `U_i`.
The supports may overlap arbitrarily; what makes RF2 degrade gracefully is
**color-disjointness** of the transpositions: for a fixed color `c` at most
one pair moves the read `ρ c`, so the color-`c` layer map is the two-valued
map of that single pair — off every other pair's support profile — and
per-color bijectivity reduces to the single-swap analysis.  Concretely:

* **Per-color RF2 criteria** (`layerMap_bijective_of_constant_read`,
  `layerMap_bijective_of_two_valued_read`): per-color refinements of E5's
  `layerMap_bijective_of_constant` / `_of_cylinder` — only the *read*
  `rowAt t w c` of the one color matters, not the whole row.
* **Multi-swap layers** (`SwapDesc`, `activeSwaps`,
  `layerMap_bijective_of_multi_swap`): if the row at `w` is `ρ` composed
  with the product of the transpositions active at `w`, the pairs are
  pairwise color-disjoint (`SwapDesc.ColorDisjoint`; the design note's
  flattened-`Nodup` condition is sufficient,
  `pairwise_colorDisjoint_of_flatten_nodup`), and each support is invariant
  under its own step-difference vector (`SwapDesc.Invariant`), then every
  color's layer map is bijective.
* **Growth-plan descriptors** (`MultiSwapDesc`, `GrowthLayerDesc`,
  `rowSchedule_layerBijective_of_growthPlan`): the bundled per-layer plan,
  extending E5's `LayerDesc` plans; old plans lift along
  `growthOfLayerDesc` (`rowSchedule_layerBijective_of_liftedPlan`).
* **Four-point growth rows** (`fourPointDesc`,
  `layerMap_bijective_of_fourPoint`): the paper's `σ_{s,δ} = (s a)(b c)` as
  a two-pair multi-swap descriptor; color-disjointness is the pairwise
  distinctness of `s, a, b, c` across the two transpositions.
* **Line/plane supports** (`lineSupport`, `planeSupport`, `lineSwapDesc`,
  `planeSwapDesc`): affine coset supports (reusing
  `EvenV11.ProjectionKernel.lineCoset` for lines) whose RF2 invariance in
  their own spanning directions is free by construction — the shapes the
  G4/G6 anchor and growth supports instantiate.
* **Anchor `n = 4, m = 4`** (`anchorDesc`, `anchor_layerBijective`,
  `anchor_layerMap_bijective_decide`): a two-pair layer `(0 1)(2 3)` on two
  crossing line supports through the origin; RF2 via the multi-swap
  criterion, cross-checked by an independent `decide` of bijectivity.

No `sorry`, no `native_decide`.
-/

namespace EvenV11
namespace V28Hard
namespace MultiSwapRowSchedule

open Shared StandardRootFlatLift EndpointRowSchedule

/-! ## Part A: per-color RF2 criteria

E5's criteria constrain the whole row `rowAt t w`; for multi-substitution
layers only the single read `rowAt t w c` of the color under scrutiny is
controlled (other pairs may change the row, but not this color's read). -/

/-- **Per-color RF2, constant-read case**: if color `c` reads the same
direction `x` at every state of the layer, its layer map is the translation
by `stepVec x`, hence bijective — no matter what the other colors read. -/
theorem layerMap_bijective_of_constant_read {n m : Nat} [NeZero m]
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (t : ZMod m) (c : TorusColor (n + 1)) (x : Fin (n + 1))
    (hconst : ∀ w, rowAt t w c = x) :
    Function.Bijective ((rowSchedule rowAt).layerMap t c) := by
  have hlayer : (rowSchedule rowAt).layerMap t c =
      fun w : RootState n m => w + stepVec x := by
    funext w
    rw [rowSchedule_layerMap_apply, hconst w]
  rw [hlayer]
  exact (Equiv.addRight (stepVec x)).bijective

/-- **Per-color RF2, two-valued-read case**: if color `c` reads `x` off a
cylinder `U` and `y` on it, and `U` is invariant under translation by the
difference vector `stepVec y - stepVec x`, then the color-`c` layer map is
bijective: it factors as translation by `stepVec x` after the cylinder
substitution by the difference vector (the per-color form of E5's
`layerMap_bijective_of_cylinder`). -/
theorem layerMap_bijective_of_two_valued_read {n m : Nat} [NeZero m]
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (t : ZMod m) (c : TorusColor (n + 1)) (x y : Fin (n + 1))
    (U : Set (RootState n m))
    (hoff : ∀ w ∉ U, rowAt t w c = x)
    (hon : ∀ w ∈ U, rowAt t w c = y)
    (hinv : ∀ w, w ∈ U ↔ (w + (stepVec y - stepVec x)) ∈ U) :
    Function.Bijective ((rowSchedule rowAt).layerMap t c) := by
  classical
  have key : (rowSchedule rowAt).layerMap t c =
      (fun w : RootState n m => w + stepVec x) ∘
        cylinderShift U (stepVec y - stepVec x) := by
    funext w
    simp only [Function.comp_apply]
    by_cases hw : w ∈ U
    · rw [cylinderShift_apply_of_mem hw, rowSchedule_layerMap_apply,
        hon w hw]
      abel
    · rw [cylinderShift_apply_of_not_mem hw,
        rowSchedule_layerMap_apply, hoff w hw]
  rw [key]
  exact (Equiv.addRight (stepVec x)).bijective.comp
    (cylinderShift_bijective U _ hinv)

/-! ## Part B: swap families and the active product -/

/-- One swap substitution datum of a multi-swap layer: the transposition
`α ↔ β` applied on the support `U` (pure data; the RF2 obligations live in
`SwapDesc.Invariant` and `MultiSwapDesc.Matches`). -/
structure SwapDesc (n m : Nat) where
  /-- First swapped direction label. -/
  α : Fin (n + 1)
  /-- Second swapped direction label. -/
  β : Fin (n + 1)
  /-- Support of the substitution. -/
  U : Set (RootState n m)

/-- RF2 invariance obligation of one swap pair: its support is closed under
translation by its own step-difference vector `stepVec β - stepVec α`. -/
def SwapDesc.Invariant {n m : Nat} (p : SwapDesc n m) : Prop :=
  ∀ w, w ∈ p.U ↔ (w + (stepVec p.β - stepVec p.α)) ∈ p.U

/-- Color-disjointness of two swap pairs: the touched label sets `{α, β}`
do not meet.  (Within-pair distinctness `α ≠ β` is *not* required: a
degenerate pair contributes the identity and is RF2-harmless.) -/
def SwapDesc.ColorDisjoint {n m : Nat} (p q : SwapDesc n m) : Prop :=
  p.α ≠ q.α ∧ p.α ≠ q.β ∧ p.β ≠ q.α ∧ p.β ≠ q.β

/-- The design note's flattened-`Nodup` color condition implies the pairwise
color-disjointness used here (it additionally forces `α ≠ β` inside each
pair, which the criterion does not need). -/
theorem pairwise_colorDisjoint_of_flatten_nodup {n m : Nat}
    (pairs : List (SwapDesc n m))
    (hnd : (pairs.flatMap fun p => [p.α, p.β]).Nodup) :
    pairs.Pairwise SwapDesc.ColorDisjoint := by
  induction pairs with
  | nil => exact List.Pairwise.nil
  | cons p rest ih =>
      rw [List.flatMap_cons, List.nodup_append'] at hnd
      refine List.Pairwise.cons (fun q hq => ?_) (ih hnd.2.1)
      have hqα : q.α ∈ rest.flatMap fun r => [r.α, r.β] :=
        List.mem_flatMap.mpr ⟨q, hq, by simp⟩
      have hqβ : q.β ∈ rest.flatMap fun r => [r.α, r.β] :=
        List.mem_flatMap.mpr ⟨q, hq, by simp⟩
      have hpα : p.α ∉ rest.flatMap fun r => [r.α, r.β] :=
        hnd.2.2 (show p.α ∈ [p.α, p.β] by simp)
      have hpβ : p.β ∉ rest.flatMap fun r => [r.α, r.β] :=
        hnd.2.2 (show p.β ∈ [p.α, p.β] by simp)
      exact ⟨fun h => hpα (by rw [h]; exact hqα),
        fun h => hpα (by rw [h]; exact hqβ),
        fun h => hpβ (by rw [h]; exact hqα),
        fun h => hpβ (by rw [h]; exact hqβ)⟩

open Classical in
/-- Product of the transpositions of the swap pairs whose supports contain
`w` (the "active" substitutions at `w`).  For color-disjoint families the
composition order is immaterial; spec-level definition, evaluated in proofs
through the `activeSwaps_cons_of_mem` / `_of_not_mem` case lemmas. -/
noncomputable def activeSwaps {n m : Nat} (pairs : List (SwapDesc n m))
    (w : RootState n m) : Equiv.Perm (Fin (n + 1)) :=
  pairs.foldr
    (fun p σ => if w ∈ p.U then Equiv.swap p.α p.β * σ else σ) 1

@[simp] theorem activeSwaps_nil {n m : Nat} (w : RootState n m) :
    activeSwaps ([] : List (SwapDesc n m)) w = 1 := rfl

/-- Case lemma: the head pair is active. -/
theorem activeSwaps_cons_of_mem {n m : Nat} {p : SwapDesc n m}
    (pairs : List (SwapDesc n m)) {w : RootState n m} (hw : w ∈ p.U) :
    activeSwaps (p :: pairs) w =
      Equiv.swap p.α p.β * activeSwaps pairs w := by
  simp only [activeSwaps, List.foldr_cons]
  exact if_pos hw

/-- Case lemma: the head pair is inactive. -/
theorem activeSwaps_cons_of_not_mem {n m : Nat} {p : SwapDesc n m}
    (pairs : List (SwapDesc n m)) {w : RootState n m} (hw : w ∉ p.U) :
    activeSwaps (p :: pairs) w = activeSwaps pairs w := by
  simp only [activeSwaps, List.foldr_cons]
  exact if_neg hw

/-- A label touched by no pair of the family is fixed by the active
product, whatever the support profile of `w` is. -/
theorem activeSwaps_apply_of_forall_notMem {n m : Nat}
    (pairs : List (SwapDesc n m)) (w : RootState n m) (x : Fin (n + 1))
    (hx : ∀ p ∈ pairs, x ≠ p.α ∧ x ≠ p.β) :
    activeSwaps pairs w x = x := by
  induction pairs with
  | nil => simp
  | cons p rest ih =>
      have hp := hx p (by simp)
      have hrest : ∀ q ∈ rest, x ≠ q.α ∧ x ≠ q.β :=
        fun q hq => hx q (List.mem_cons_of_mem _ hq)
      by_cases hw : w ∈ p.U
      · rw [activeSwaps_cons_of_mem rest hw, Equiv.Perm.mul_apply,
          ih hrest, Equiv.swap_apply_of_ne_of_ne hp.1 hp.2]
      · rw [activeSwaps_cons_of_not_mem rest hw, ih hrest]

/-- A transposition color-disjoint from the pair `p` fixes `p`'s labels. -/
theorem swap_apply_of_colorDisjoint {n m : Nat} {q p : SwapDesc n m}
    (hqp : q.ColorDisjoint p) {x : Fin (n + 1)}
    (hx : x = p.α ∨ x = p.β) :
    Equiv.swap q.α q.β x = x := by
  rcases hx with rfl | rfl
  · exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hqp.1)
      (Ne.symm hqp.2.2.1)
  · exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hqp.2.1)
      (Ne.symm hqp.2.2.2)

/-- Pairs color-disjoint from `p` touch neither of `p`'s labels. -/
theorem forall_notMem_of_colorDisjoint_head {n m : Nat}
    {p : SwapDesc n m} {rest : List (SwapDesc n m)}
    (hdisj : ∀ r ∈ rest, p.ColorDisjoint r) {x : Fin (n + 1)}
    (hx : x = p.α ∨ x = p.β) :
    ∀ r ∈ rest, x ≠ r.α ∧ x ≠ r.β := by
  intro r hr
  have hpr := hdisj r hr
  rcases hx with rfl | rfl
  · exact ⟨hpr.1, hpr.2.1⟩
  · exact ⟨hpr.2.2.1, hpr.2.2.2⟩

/-- **The disjointness reduction, on-support case**: on `p`'s support, the
active product moves a label of `p` exactly as `p`'s own transposition —
all other pairs are silenced by color-disjointness, regardless of how their
supports overlap `p`'s. -/
theorem activeSwaps_apply_of_mem {n m : Nat}
    (pairs : List (SwapDesc n m)) {p : SwapDesc n m} {x : Fin (n + 1)}
    {w : RootState n m}
    (hdisj : pairs.Pairwise SwapDesc.ColorDisjoint) (hp : p ∈ pairs)
    (hx : x = p.α ∨ x = p.β) (hw : w ∈ p.U) :
    activeSwaps pairs w x = Equiv.swap p.α p.β x := by
  induction pairs with
  | nil => cases hp
  | cons q rest ih =>
      rw [List.pairwise_cons] at hdisj
      rcases List.mem_cons.mp hp with rfl | hpr
      · have hxr : activeSwaps rest w x = x :=
          activeSwaps_apply_of_forall_notMem rest w x
            (forall_notMem_of_colorDisjoint_head hdisj.1 hx)
        rw [activeSwaps_cons_of_mem rest hw, Equiv.Perm.mul_apply, hxr]
      · have hx' : Equiv.swap p.α p.β x = p.α ∨
            Equiv.swap p.α p.β x = p.β := by
          rcases hx with rfl | rfl
          · exact Or.inr (Equiv.swap_apply_left _ _)
          · exact Or.inl (Equiv.swap_apply_right _ _)
        by_cases hwq : w ∈ q.U
        · rw [activeSwaps_cons_of_mem rest hwq, Equiv.Perm.mul_apply,
            ih hdisj.2 hpr,
            swap_apply_of_colorDisjoint (hdisj.1 p hpr) hx']
        · rw [activeSwaps_cons_of_not_mem rest hwq, ih hdisj.2 hpr]

/-- **The disjointness reduction, off-support case**: off `p`'s support,
the active product fixes `p`'s labels — `p` is inactive and every other
pair is silenced by color-disjointness. -/
theorem activeSwaps_apply_of_not_mem {n m : Nat}
    (pairs : List (SwapDesc n m)) {p : SwapDesc n m} {x : Fin (n + 1)}
    {w : RootState n m}
    (hdisj : pairs.Pairwise SwapDesc.ColorDisjoint) (hp : p ∈ pairs)
    (hx : x = p.α ∨ x = p.β) (hw : w ∉ p.U) :
    activeSwaps pairs w x = x := by
  induction pairs with
  | nil => cases hp
  | cons q rest ih =>
      rw [List.pairwise_cons] at hdisj
      rcases List.mem_cons.mp hp with rfl | hpr
      · have hxr : activeSwaps rest w x = x :=
          activeSwaps_apply_of_forall_notMem rest w x
            (forall_notMem_of_colorDisjoint_head hdisj.1 hx)
        rw [activeSwaps_cons_of_not_mem rest hw, hxr]
      · by_cases hwq : w ∈ q.U
        · rw [activeSwaps_cons_of_mem rest hwq, Equiv.Perm.mul_apply,
            ih hdisj.2 hpr,
            swap_apply_of_colorDisjoint (hdisj.1 p hpr) hx]
        · rw [activeSwaps_cons_of_not_mem rest hwq, ih hdisj.2 hpr]

/-! ## Part C: RF2 for multi-swap layers -/

/-- **RF2, disjoint multi-swap case** (G1): a layer whose row at `w` is the
base permutation `ρ` composed with the product of the swap substitutions
active at `w` has bijective layer maps in every color, provided the pairs
are pairwise color-disjoint and each support is invariant under its own
step-difference vector.  Supports may overlap arbitrarily: for a fixed
color `c` at most one pair moves the read `ρ c`, so the color-`c` layer map
is the two-valued map of that pair alone and the single-swap analysis
applies; untouched colors translate constantly. -/
theorem layerMap_bijective_of_multi_swap {n m : Nat} [NeZero m]
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (t : ZMod m) (ρ : Equiv.Perm (Fin (n + 1)))
    (pairs : List (SwapDesc n m))
    (hdisj : pairs.Pairwise SwapDesc.ColorDisjoint)
    (hinv : ∀ p ∈ pairs, p.Invariant)
    (hrow : ∀ w, rowAt t w = ρ.trans (activeSwaps pairs w)) :
    ∀ c, Function.Bijective ((rowSchedule rowAt).layerMap t c) := by
  intro c
  have hread : ∀ w, rowAt t w c = activeSwaps pairs w (ρ c) := by
    intro w
    rw [hrow w]
    rfl
  by_cases hmem : ∃ p ∈ pairs, ρ c = p.α ∨ ρ c = p.β
  · obtain ⟨p, hp, hx⟩ := hmem
    refine layerMap_bijective_of_two_valued_read rowAt t c (ρ c)
      (Equiv.swap p.α p.β (ρ c)) p.U ?_ ?_ ?_
    · intro w hw
      rw [hread w, activeSwaps_apply_of_not_mem pairs hdisj hp hx hw]
    · intro w hw
      rw [hread w, activeSwaps_apply_of_mem pairs hdisj hp hx hw]
    · have hpinv := hinv p hp
      rcases hx with hxa | hxb
      · intro w
        rw [hxa, Equiv.swap_apply_left]
        exact hpinv w
      · intro w
        rw [hxb, Equiv.swap_apply_right]
        have h := mem_iff_add_neg_mem hpinv w
        rwa [neg_sub] at h
  · refine layerMap_bijective_of_constant_read rowAt t c (ρ c) ?_
    intro w
    rw [hread w,
      activeSwaps_apply_of_forall_notMem pairs w (ρ c) fun p hp =>
        ⟨fun ha => hmem ⟨p, hp, Or.inl ha⟩,
          fun hb => hmem ⟨p, hp, Or.inr hb⟩⟩]

/-- Multi-substitution layer descriptor: a base permutation with a family
of swap substitutions, each on its own support (pure data; obligations in
`MultiSwapDesc.Matches`). -/
structure MultiSwapDesc (n m : Nat) where
  /-- Base row permutation of the layer. -/
  base : Equiv.Perm (Fin (n + 1))
  /-- The swap substitutions of the layer. -/
  pairs : List (SwapDesc n m)

/-- The RF2 obligations tying a multi-swap descriptor to the row family at
layer `t`: the pairs are pairwise color-disjoint, every support satisfies
its own invariance, and the row at each `w` is the base composed with the
product of the substitutions active at `w`. -/
def MultiSwapDesc.Matches {n m : Nat}
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (t : ZMod m) (D : MultiSwapDesc n m) : Prop :=
  D.pairs.Pairwise SwapDesc.ColorDisjoint ∧
    (∀ p ∈ D.pairs, p.Invariant) ∧
    ∀ w, rowAt t w = D.base.trans (activeSwaps D.pairs w)

/-- **RF2 from a matching multi-swap descriptor**, in every color. -/
theorem layerMap_bijective_of_multiSwapDesc {n m : Nat} [NeZero m]
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (t : ZMod m) (D : MultiSwapDesc n m) (hmatch : D.Matches rowAt t) :
    ∀ c, Function.Bijective ((rowSchedule rowAt).layerMap t c) :=
  layerMap_bijective_of_multi_swap rowAt t D.base D.pairs
    hmatch.1 hmatch.2.1 hmatch.2.2

/-! ## Part D: growth-plan descriptors and the E5 lift -/

/-- Per-layer RF2 descriptor for the growth engine: at each layer the row
is either a fixed permutation or a multi-swap substitution family over a
base permutation.  Extends E5's `LayerDesc` (which embeds along
`growthOfLayerDesc`). -/
inductive GrowthLayerDesc (n m : Nat) where
  /-- The row at this layer is constantly `ρ`. -/
  | const (ρ : Equiv.Perm (Fin (n + 1)))
  /-- The row at this layer is described by the multi-swap descriptor. -/
  | multiSwap (D : MultiSwapDesc n m)

/-- The RF2 obligations tying a growth layer descriptor to the actual row
family at layer `t`. -/
def GrowthLayerDesc.Matches {n m : Nat}
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (t : ZMod m) : GrowthLayerDesc n m → Prop
  | const ρ => ∀ w, rowAt t w = ρ
  | multiSwap D => D.Matches rowAt t

/-- **Bundled RF2 for growth plans**: if every layer has a matching growth
descriptor, the whole row schedule is `layerBijective`. -/
theorem rowSchedule_layerBijective_of_growthPlan {n m : Nat} [NeZero m]
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (plan : ZMod m → GrowthLayerDesc n m)
    (hplan : ∀ t, (plan t).Matches rowAt t) :
    (rowSchedule rowAt).layerBijective := by
  intro t c
  have h := hplan t
  cases hp : plan t with
  | const ρ =>
      rw [hp] at h
      exact layerMap_bijective_of_constant rowAt t c ρ h
  | multiSwap D =>
      rw [hp] at h
      exact layerMap_bijective_of_multiSwapDesc rowAt t D h c

/-- Embedding of E5 layer descriptors into growth descriptors: constants
stay constants, a swap-on-cylinder becomes a one-pair multi-swap. -/
def growthOfLayerDesc {n m : Nat} : LayerDesc n m → GrowthLayerDesc n m
  | .const ρ => .const ρ
  | .swapCylinder ρ α β U => .multiSwap ⟨ρ, [⟨α, β, U⟩]⟩

/-- The embedding preserves `Matches`: an E5 layer plan entry that matches
in the old sense matches its lifted growth descriptor. -/
theorem growthOfLayerDesc_matches {n m : Nat}
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (t : ZMod m) (d : LayerDesc n m) (h : d.Matches rowAt t) :
    (growthOfLayerDesc d).Matches rowAt t := by
  cases d with
  | const ρ => exact h
  | swapCylinder ρ α β U =>
      obtain ⟨hoff, hon, hinv⟩ := h
      have hpw : List.Pairwise SwapDesc.ColorDisjoint
          [(⟨α, β, U⟩ : SwapDesc n m)] :=
        List.Pairwise.cons (fun r hr => nomatch hr) List.Pairwise.nil
      have hinv' : ∀ p ∈ [(⟨α, β, U⟩ : SwapDesc n m)], p.Invariant := by
        intro p hp
        rw [List.mem_singleton] at hp
        subst hp
        exact hinv
      have hrow : ∀ w, rowAt t w =
          ρ.trans (activeSwaps [(⟨α, β, U⟩ : SwapDesc n m)] w) := by
        intro w
        by_cases hw : w ∈ U
        · rw [activeSwaps_cons_of_mem _ hw, activeSwaps_nil, mul_one]
          exact hon w hw
        · rw [activeSwaps_cons_of_not_mem _ hw, activeSwaps_nil,
            Equiv.Perm.one_def, Equiv.trans_refl]
          exact hoff w hw
      exact ⟨hpw, hinv', hrow⟩

/-- **Existing E5 plans lift**: a per-layer `LayerDesc` plan yields the
full RF2 certificate through the growth-descriptor route (re-deriving E5's
`rowSchedule_layerBijective_of_plan` inside the new framework). -/
theorem rowSchedule_layerBijective_of_liftedPlan {n m : Nat} [NeZero m]
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (plan : ZMod m → LayerDesc n m)
    (hplan : ∀ t, (plan t).Matches rowAt t) :
    (rowSchedule rowAt).layerBijective :=
  rowSchedule_layerBijective_of_growthPlan rowAt
    (fun t => growthOfLayerDesc (plan t))
    (fun t => growthOfLayerDesc_matches rowAt t (plan t) (hplan t))

/-! ## Part E: four-point growth rows `σ_{s,δ} = (s a)(b c)` -/

/-- Four-point growth-row descriptor: the paper's `σ_{s,δ} = (s a)(b c)` —
the leaf swap `(s a)` substituted on `U₁` and the quotient swap `(b c)` on
`U₂`, over the base row `ρ`.  Color-disjointness is the pairwise
distinctness of `s, a` against `b, c`. -/
def fourPointDesc {n m : Nat} (ρ : Equiv.Perm (Fin (n + 1)))
    (s a b c : Fin (n + 1)) (U₁ U₂ : Set (RootState n m)) :
    MultiSwapDesc n m :=
  ⟨ρ, [⟨s, a, U₁⟩, ⟨b, c, U₂⟩]⟩

/-- `Matches` builder for a four-point layer from the four
membership-profile row equations.  (The two swaps are color-disjoint, so
they commute; the both-supports row is stated in `activeSwaps` order
`(s a) * (b c)`.) -/
theorem fourPointDesc_matches {n m : Nat}
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (t : ZMod m) (ρ : Equiv.Perm (Fin (n + 1)))
    (s a b c : Fin (n + 1)) (U₁ U₂ : Set (RootState n m))
    (hsb : s ≠ b) (hsc : s ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hinv₁ : ∀ w, w ∈ U₁ ↔ (w + (stepVec a - stepVec s)) ∈ U₁)
    (hinv₂ : ∀ w, w ∈ U₂ ↔ (w + (stepVec c - stepVec b)) ∈ U₂)
    (hoff : ∀ w, w ∉ U₁ → w ∉ U₂ → rowAt t w = ρ)
    (hon₁ : ∀ w, w ∈ U₁ → w ∉ U₂ →
      rowAt t w = ρ.trans (Equiv.swap s a))
    (hon₂ : ∀ w, w ∉ U₁ → w ∈ U₂ →
      rowAt t w = ρ.trans (Equiv.swap b c))
    (hon₁₂ : ∀ w, w ∈ U₁ → w ∈ U₂ →
      rowAt t w = ρ.trans (Equiv.swap s a * Equiv.swap b c)) :
    (fourPointDesc ρ s a b c U₁ U₂).Matches rowAt t := by
  have hpw : List.Pairwise SwapDesc.ColorDisjoint
      [(⟨s, a, U₁⟩ : SwapDesc n m), ⟨b, c, U₂⟩] := by
    refine List.Pairwise.cons (fun q hq => ?_)
      (List.Pairwise.cons (fun r hr => nomatch hr) List.Pairwise.nil)
    rw [List.mem_singleton] at hq
    subst hq
    exact ⟨hsb, hsc, hab, hac⟩
  have hinv : ∀ p ∈ [(⟨s, a, U₁⟩ : SwapDesc n m), ⟨b, c, U₂⟩],
      p.Invariant := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hinv₁
    · rw [List.mem_singleton] at hp
      subst hp
      exact hinv₂
  have hrow : ∀ w, rowAt t w = ρ.trans
      (activeSwaps [(⟨s, a, U₁⟩ : SwapDesc n m), ⟨b, c, U₂⟩] w) := by
    intro w
    by_cases hw₁ : w ∈ U₁ <;> by_cases hw₂ : w ∈ U₂
    · rw [activeSwaps_cons_of_mem _ hw₁, activeSwaps_cons_of_mem _ hw₂,
        activeSwaps_nil, mul_one]
      exact hon₁₂ w hw₁ hw₂
    · rw [activeSwaps_cons_of_mem _ hw₁,
        activeSwaps_cons_of_not_mem _ hw₂, activeSwaps_nil, mul_one]
      exact hon₁ w hw₁ hw₂
    · rw [activeSwaps_cons_of_not_mem _ hw₁,
        activeSwaps_cons_of_mem _ hw₂, activeSwaps_nil, mul_one]
      exact hon₂ w hw₁ hw₂
    · rw [activeSwaps_cons_of_not_mem _ hw₁,
        activeSwaps_cons_of_not_mem _ hw₂, activeSwaps_nil,
        Equiv.Perm.one_def, Equiv.trans_refl]
      exact hoff w hw₁ hw₂
  exact ⟨hpw, hinv, hrow⟩

/-- **RF2 for four-point growth layers**, in every color: the paper's
`σ_{s,δ} = (s a)(b c)` row substituted on the (possibly overlapping)
supports `U₁`, `U₂`, each invariant under its own swap direction. -/
theorem layerMap_bijective_of_fourPoint {n m : Nat} [NeZero m]
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (t : ZMod m) (ρ : Equiv.Perm (Fin (n + 1)))
    (s a b c : Fin (n + 1)) (U₁ U₂ : Set (RootState n m))
    (hsb : s ≠ b) (hsc : s ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hinv₁ : ∀ w, w ∈ U₁ ↔ (w + (stepVec a - stepVec s)) ∈ U₁)
    (hinv₂ : ∀ w, w ∈ U₂ ↔ (w + (stepVec c - stepVec b)) ∈ U₂)
    (hoff : ∀ w, w ∉ U₁ → w ∉ U₂ → rowAt t w = ρ)
    (hon₁ : ∀ w, w ∈ U₁ → w ∉ U₂ →
      rowAt t w = ρ.trans (Equiv.swap s a))
    (hon₂ : ∀ w, w ∉ U₁ → w ∈ U₂ →
      rowAt t w = ρ.trans (Equiv.swap b c))
    (hon₁₂ : ∀ w, w ∈ U₁ → w ∈ U₂ →
      rowAt t w = ρ.trans (Equiv.swap s a * Equiv.swap b c)) :
    ∀ c₀, Function.Bijective ((rowSchedule rowAt).layerMap t c₀) :=
  layerMap_bijective_of_multiSwapDesc rowAt t
    (fourPointDesc ρ s a b c U₁ U₂)
    (fourPointDesc_matches rowAt t ρ s a b c U₁ U₂ hsb hsc hab hac
      hinv₁ hinv₂ hoff hon₁ hon₂ hon₁₂)

/-! ## Part F: line and plane supports

The anchor/growth supports are cosets of subgroups spanned by step-vector
differences; their RF2 invariance in the spanning directions holds by
construction.  Lines reuse `EvenV11.ProjectionKernel.lineCoset` (the
`Vec m n` of `ProjectionKernel` is definitionally `RootState n m`). -/

/-- Affine line support: the coset `w₀ + ⟨d⟩` of the cyclic subgroup
generated by `d`, as a set of root states (membership is
`ProjectionKernel.lineCoset d w₀`). -/
def lineSupport {n m : Nat} (w₀ d : RootState n m) :
    Set (RootState n m) :=
  {w | ProjectionKernel.lineCoset d w₀ w}

/-- Membership unfolding for `lineSupport`. -/
theorem mem_lineSupport {n m : Nat} (w₀ d w : RootState n m) :
    w ∈ lineSupport w₀ d ↔ ∃ a : ZMod m, w = fun i => w₀ i + a * d i :=
  Iff.rfl

/-- The base point lies on its line. -/
theorem self_mem_lineSupport {n m : Nat} (w₀ d : RootState n m) :
    w₀ ∈ lineSupport w₀ d :=
  ⟨0, by funext i; simp⟩

/-- **Line invariance, free by construction**: a line support is invariant
under translation by its own direction vector. -/
theorem lineSupport_invariant {n m : Nat} (w₀ d : RootState n m) :
    ∀ w, w ∈ lineSupport w₀ d ↔ (w + d) ∈ lineSupport w₀ d := by
  intro w
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a + 1, ?_⟩
    funext i
    simp only [Pi.add_apply]
    ring
  · rintro ⟨a, ha⟩
    refine ⟨a - 1, ?_⟩
    funext i
    have hi := congrFun ha i
    simp only [Pi.add_apply] at hi
    have hw : w i = w₀ i + a * d i - d i := by
      rw [← hi]
      ring
    rw [hw]
    ring

/-- Decidable membership in a line support (drives the `decide` anchors). -/
instance decidableMemLineSupport {n m : Nat} [NeZero m]
    (w₀ d : RootState n m) : DecidablePred (· ∈ lineSupport w₀ d) :=
  fun w => decidable_of_iff
    (∃ a : ZMod m, w = fun i => w₀ i + a * d i) Iff.rfl

/-- Affine plane support: the coset `w₀ + ⟨d₁, d₂⟩` of the subgroup
generated by two direction vectors (the paper's common plane-closed
four-point support shape). -/
def planeSupport {n m : Nat} (w₀ d₁ d₂ : RootState n m) :
    Set (RootState n m) :=
  {w | ∃ a b : ZMod m, w = fun i => w₀ i + a * d₁ i + b * d₂ i}

/-- Membership unfolding for `planeSupport`. -/
theorem mem_planeSupport {n m : Nat} (w₀ d₁ d₂ w : RootState n m) :
    w ∈ planeSupport w₀ d₁ d₂ ↔
      ∃ a b : ZMod m, w = fun i => w₀ i + a * d₁ i + b * d₂ i :=
  Iff.rfl

/-- A plane support is `ProjectionKernel.translatedTwoLineSet` over the
one-point base set `{w₀}` — the kernel files' shape. -/
theorem mem_planeSupport_iff_translatedTwoLineSet {n m : Nat}
    (w₀ d₁ d₂ w : RootState n m) :
    w ∈ planeSupport w₀ d₁ d₂ ↔
      ProjectionKernel.translatedTwoLineSet (· = w₀) d₁ d₂ w := by
  constructor
  · rintro ⟨a, b, hw⟩
    exact ⟨w₀, a, b, rfl, hw⟩
  · rintro ⟨h, a, b, hh, hw⟩
    subst hh
    exact ⟨a, b, hw⟩

/-- **Plane invariance in the first direction**, free by construction. -/
theorem planeSupport_invariant_fst {n m : Nat}
    (w₀ d₁ d₂ : RootState n m) :
    ∀ w, w ∈ planeSupport w₀ d₁ d₂ ↔
      (w + d₁) ∈ planeSupport w₀ d₁ d₂ := by
  intro w
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨a + 1, b, ?_⟩
    funext i
    simp only [Pi.add_apply]
    ring
  · rintro ⟨a, b, ha⟩
    refine ⟨a - 1, b, ?_⟩
    funext i
    have hi := congrFun ha i
    simp only [Pi.add_apply] at hi
    have hw : w i = w₀ i + a * d₁ i + b * d₂ i - d₁ i := by
      rw [← hi]
      ring
    rw [hw]
    ring

/-- **Plane invariance in the second direction**, free by construction. -/
theorem planeSupport_invariant_snd {n m : Nat}
    (w₀ d₁ d₂ : RootState n m) :
    ∀ w, w ∈ planeSupport w₀ d₁ d₂ ↔
      (w + d₂) ∈ planeSupport w₀ d₁ d₂ := by
  intro w
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨a, b + 1, ?_⟩
    funext i
    simp only [Pi.add_apply]
    ring
  · rintro ⟨a, b, ha⟩
    refine ⟨a, b - 1, ?_⟩
    funext i
    have hi := congrFun ha i
    simp only [Pi.add_apply] at hi
    have hw : w i = w₀ i + a * d₁ i + b * d₂ i - d₂ i := by
      rw [← hi]
      ring
    rw [hw]
    ring

/-- Decidable membership in a plane support. -/
instance decidableMemPlaneSupport {n m : Nat} [NeZero m]
    (w₀ d₁ d₂ : RootState n m) :
    DecidablePred (· ∈ planeSupport w₀ d₁ d₂) :=
  fun w => decidable_of_iff
    (∃ a b : ZMod m, w = fun i => w₀ i + a * d₁ i + b * d₂ i) Iff.rfl

/-- Swap pair on the line through `w₀` in its own step-difference
direction: the RF2 invariance obligation is discharged by construction
(`lineSwapDesc_invariant`). -/
def lineSwapDesc {n m : Nat} (α β : Fin (n + 1)) (w₀ : RootState n m) :
    SwapDesc n m :=
  ⟨α, β, lineSupport w₀ (stepVec β - stepVec α)⟩

/-- A line swap pair is invariant for free. -/
theorem lineSwapDesc_invariant {n m : Nat} (α β : Fin (n + 1))
    (w₀ : RootState n m) : (lineSwapDesc α β w₀).Invariant :=
  fun w => lineSupport_invariant w₀ (stepVec β - stepVec α) w

/-- Swap pair on the plane through `w₀` spanned by its own step-difference
direction and a second direction `d'` (e.g. the other swap's direction, for
the paper's common plane-closed four-point support). -/
def planeSwapDesc {n m : Nat} (α β : Fin (n + 1))
    (w₀ d' : RootState n m) : SwapDesc n m :=
  ⟨α, β, planeSupport w₀ (stepVec β - stepVec α) d'⟩

/-- A plane swap pair is invariant for free (in its own direction). -/
theorem planeSwapDesc_invariant {n m : Nat} (α β : Fin (n + 1))
    (w₀ d' : RootState n m) : (planeSwapDesc α β w₀ d').Invariant :=
  fun w => planeSupport_invariant_fst w₀ (stepVec β - stepVec α) d' w

/-- Four-point descriptor on two separate line supports, each in its own
swap direction (the paper's separate-supports shape; the invariance
obligations vanish). -/
def fourPointLineDesc {n m : Nat} (ρ : Equiv.Perm (Fin (n + 1)))
    (s a b c : Fin (n + 1)) (w₁ w₂ : RootState n m) :
    MultiSwapDesc n m :=
  ⟨ρ, [lineSwapDesc s a w₁, lineSwapDesc b c w₂]⟩

/-- The line-supported four-point descriptor is the generic one at the two
line cosets. -/
theorem fourPointLineDesc_eq {n m : Nat} (ρ : Equiv.Perm (Fin (n + 1)))
    (s a b c : Fin (n + 1)) (w₁ w₂ : RootState n m) :
    fourPointLineDesc ρ s a b c w₁ w₂ =
      fourPointDesc ρ s a b c
        (lineSupport w₁ (stepVec a - stepVec s))
        (lineSupport w₂ (stepVec c - stepVec b)) := rfl

/-- **RF2 for four-point layers on two line supports**: the invariance
obligations are free, leaving only color-disjointness and the four
membership-profile row equations. -/
theorem layerMap_bijective_of_fourPoint_lines {n m : Nat} [NeZero m]
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (t : ZMod m) (ρ : Equiv.Perm (Fin (n + 1)))
    (s a b c : Fin (n + 1)) (w₁ w₂ : RootState n m)
    (hsb : s ≠ b) (hsc : s ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hoff : ∀ w, w ∉ lineSupport w₁ (stepVec a - stepVec s) →
      w ∉ lineSupport w₂ (stepVec c - stepVec b) → rowAt t w = ρ)
    (hon₁ : ∀ w, w ∈ lineSupport w₁ (stepVec a - stepVec s) →
      w ∉ lineSupport w₂ (stepVec c - stepVec b) →
      rowAt t w = ρ.trans (Equiv.swap s a))
    (hon₂ : ∀ w, w ∉ lineSupport w₁ (stepVec a - stepVec s) →
      w ∈ lineSupport w₂ (stepVec c - stepVec b) →
      rowAt t w = ρ.trans (Equiv.swap b c))
    (hon₁₂ : ∀ w, w ∈ lineSupport w₁ (stepVec a - stepVec s) →
      w ∈ lineSupport w₂ (stepVec c - stepVec b) →
      rowAt t w = ρ.trans (Equiv.swap s a * Equiv.swap b c)) :
    ∀ c₀, Function.Bijective ((rowSchedule rowAt).layerMap t c₀) :=
  layerMap_bijective_of_fourPoint rowAt t ρ s a b c _ _
    hsb hsc hab hac
    (lineSupport_invariant w₁ (stepVec a - stepVec s))
    (lineSupport_invariant w₂ (stepVec c - stepVec b))
    hoff hon₁ hon₂ hon₁₂

/-! ## Part G: the `n = 4, m = 4` anchor

A two-pair layer `(0 1)(2 3)` over the neutral base row, on two *crossing*
line supports through the origin (they meet exactly at `0` and each leaves
the other).  RF2 follows from the multi-swap criterion; an independent
`decide` re-verifies bijectivity pointwise. -/

/-- Anchor pair 1: swap `0 ↔ 1` on the line through the origin in direction
`stepVec 1 - stepVec 0`. -/
def anchorPair₁ : SwapDesc 4 4 := lineSwapDesc 0 1 0

/-- Anchor pair 2: swap `2 ↔ 3` on the line through the origin in direction
`stepVec 3 - stepVec 2`. -/
def anchorPair₂ : SwapDesc 4 4 := lineSwapDesc 2 3 0

instance : DecidablePred (· ∈ anchorPair₁.U) :=
  fun w => decidableMemLineSupport 0 (stepVec 1 - stepVec 0) w

instance : DecidablePred (· ∈ anchorPair₂.U) :=
  fun w => decidableMemLineSupport 0 (stepVec 3 - stepVec 2) w

/-- The concrete anchor row family (constant in the layer index): neutral
base row with the two anchor swaps applied on their supports. -/
def anchorRowAt (_t : ZMod 4) (w : RootState 4 4) :
    Equiv.Perm (Fin 5) :=
  (if w ∈ anchorPair₁.U then Equiv.swap anchorPair₁.α anchorPair₁.β
    else 1) *
    (if w ∈ anchorPair₂.U then Equiv.swap anchorPair₂.α anchorPair₂.β
      else 1)

/-- The anchor multi-swap descriptor: base `1` with the two crossing line
pairs. -/
def anchorDesc : MultiSwapDesc 4 4 := ⟨1, [anchorPair₁, anchorPair₂]⟩

/-- The anchor row family matches its descriptor. -/
theorem anchorDesc_matches (t : ZMod 4) :
    anchorDesc.Matches anchorRowAt t := by
  have hpw : List.Pairwise SwapDesc.ColorDisjoint
      [anchorPair₁, anchorPair₂] := by
    refine List.Pairwise.cons (fun q hq => ?_)
      (List.Pairwise.cons (fun r hr => nomatch hr) List.Pairwise.nil)
    rw [List.mem_singleton] at hq
    subst hq
    refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
  have hinv : ∀ p ∈ [anchorPair₁, anchorPair₂], p.Invariant := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact lineSwapDesc_invariant 0 1 0
    · rw [List.mem_singleton] at hp
      subst hp
      exact lineSwapDesc_invariant 2 3 0
  have hrow : ∀ w, anchorRowAt t w =
      (1 : Equiv.Perm (Fin 5)).trans
        (activeSwaps [anchorPair₁, anchorPair₂] w) := by
    intro w
    rw [Equiv.Perm.one_def, Equiv.refl_trans]
    simp only [anchorRowAt]
    by_cases h₁ : w ∈ anchorPair₁.U <;> by_cases h₂ : w ∈ anchorPair₂.U
    · rw [if_pos h₁, if_pos h₂, activeSwaps_cons_of_mem _ h₁,
        activeSwaps_cons_of_mem _ h₂, activeSwaps_nil, mul_one]
    · rw [if_pos h₁, if_neg h₂, activeSwaps_cons_of_mem _ h₁,
        activeSwaps_cons_of_not_mem _ h₂, activeSwaps_nil]
    · rw [if_neg h₁, if_pos h₂, activeSwaps_cons_of_not_mem _ h₁,
        activeSwaps_cons_of_mem _ h₂, activeSwaps_nil, mul_one,
        one_mul]
    · rw [if_neg h₁, if_neg h₂, activeSwaps_cons_of_not_mem _ h₁,
        activeSwaps_cons_of_not_mem _ h₂, activeSwaps_nil, one_mul]
  exact ⟨hpw, hinv, hrow⟩

/-- The two anchor supports genuinely cross: both contain the origin, and
the first line leaves the second (single-point `decide`s). -/
theorem anchor_supports_cross :
    (0 : RootState 4 4) ∈ anchorPair₁.U ∧
      (0 : RootState 4 4) ∈ anchorPair₂.U ∧
      stepVec (1 : Fin 5) - stepVec 0 ∈ anchorPair₁.U ∧
      stepVec (1 : Fin 5) - stepVec 0 ∉ anchorPair₂.U := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **RF2 at the anchor, via the multi-swap criterion**: every layer and
every color of the anchor schedule has a bijective layer map. -/
theorem anchor_layerBijective :
    (rowSchedule anchorRowAt).layerBijective :=
  rowSchedule_layerBijective_of_growthPlan anchorRowAt
    (fun _ => .multiSwap anchorDesc) (fun t => anchorDesc_matches t)

set_option maxRecDepth 8192 in
/-- Independent `decide` sanity cross-check of the anchor RF2: pointwise
bijectivity of the explicit layer maps, kernel-checked over all `4^4`
root states and all five colors. -/
theorem anchor_layerMap_bijective_decide :
    ∀ c : Fin 5, Function.Bijective
      (fun w : RootState 4 4 => w + stepVec (anchorRowAt 0 w c)) := by
  decide +kernel

/-- The `decide` cross-check verifies the same maps as the criterion: the
layer maps of `rowSchedule anchorRowAt` at layer `0`. -/
theorem anchor_layerMap_bijective_cross_check (c : TorusColor 5) :
    Function.Bijective
      ((rowSchedule anchorRowAt).layerMap (0 : ZMod 4) c) := by
  have he : (rowSchedule anchorRowAt).layerMap (0 : ZMod 4) c =
      fun w : RootState 4 4 => w + stepVec (anchorRowAt 0 w c) := by
    funext w
    exact rowSchedule_layerMap_apply anchorRowAt 0 c w
  rw [he]
  exact anchor_layerMap_bijective_decide c

end MultiSwapRowSchedule
end V28Hard
end EvenV11
