import Shared.Monodromy

/-!
# Skew-product holonomy single-cycle engine

This file ports the manuscript's *skew-product holonomy* lemma
(`root_flat_first_returns.tex`, `lem:skew-product-holonomy`) as a clean, general,
reusable engine.

Let `T` be a cyclic permutation (`IsSingleCycleMap`) of a finite type `Q`, let `Y`
be a finite type, and let `A : Q → Equiv.Perm Y` be a family of permutations of the
fibre.  The *skew product* is

  `S (q, y) = (T q, A q y)`.

Fix `q0 : Q` and set `N = Fintype.card Q`.  The **holonomy** around the `T`-cycle
based at `q0` is the ordered product

  `W_{q0} = A (T^[N-1] q0) ∘ ⋯ ∘ A (T q0) ∘ A q0`.

The crux identity is `S^[N] (q0, y) = (q0, W_{q0} y)` — one period of the base
returns to the fibre with the holonomy applied.  Hence the `S`-orbit structure on
`{q0} × Y` is governed by `W_{q0}`, and:

  **`S` is a single cycle iff `W_{q0}` is a single cycle.**

We prove the forward direction (the one needed downstream) and the `iff`.

The engine is built on top of the existing
`Shared.single_cycle_of_skewProduct_base_orbit_monodromy` (`Shared/Monodromy.lean`),
which already packages the orbit combinatorics.  The genuinely new content here is

* the bridge from `IsSingleCycleMap T` on a finite type to the three concrete base
  facts the cover lemma needs (`T^[N] q0 = q0`; every base point reached in `< N`
  steps; `N = Fintype.card Q`), proved via `Function.minimalPeriod`, and
* the identification of the section-return map of the skew product with the
  holonomy fold (`sectionReturn S q0 N = W_{q0}`).
-/

namespace Shared

open Function

section BaseCycle

variable {Q : Type*} [Fintype Q] (T : Q → Q)

/-- The minimal period of a single-cycle map of a finite type at any basepoint is
the cardinality of the type.  The orbit `{T^[k] q0 : k < minimalPeriod}` is a set
of `minimalPeriod`-many distinct points (`iterate_injOn_Iio_minimalPeriod`) and, by
transitivity of the single cycle (reduced mod the period), exhausts `Q`; hence its
size is `card Q`. -/
theorem isSingleCycleMap_minimalPeriod_eq_card (hT : IsSingleCycleMap T) (q0 : Q) :
    Function.minimalPeriod T q0 = Fintype.card Q := by
  classical
  -- `q0` is a periodic point (T injective on a finite type), so the period is positive.
  have hper : q0 ∈ Function.periodicPts T :=
    (hT.1.1).mem_periodicPts q0
  have hPpos : 0 < Function.minimalPeriod T q0 :=
    Function.minimalPeriod_pos_of_mem_periodicPts hper
  set P := Function.minimalPeriod T q0 with hPdef
  -- The map `k ↦ T^[k] q0` restricted to `Finset.range P` is injective into `Q`.
  have hinj : Set.InjOn (fun k => T^[k] q0) (Finset.range P) := by
    intro i hi j hj hij
    have hii : i ∈ Set.Iio P := by simpa using Finset.mem_range.mp hi
    have hjj : j ∈ Set.Iio P := by simpa using Finset.mem_range.mp hj
    exact Function.iterate_injOn_Iio_minimalPeriod hii hjj hij
  -- The image has size `P`.
  have hcardimg :
      (Finset.image (fun k => T^[k] q0) (Finset.range P)).card = P := by
    rw [Finset.card_image_of_injOn hinj]; simp
  -- Every `q : Q` lies in the image: reduce the transitivity witness mod `P`.
  have hsurj : Finset.image (fun k => T^[k] q0) (Finset.range P) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro q
    rcases hT.2 q0 q with ⟨n, hn⟩
    refine Finset.mem_image.mpr ⟨n % P, ?_, ?_⟩
    · exact Finset.mem_range.mpr (Nat.mod_lt _ hPpos)
    · rw [Function.iterate_mod_minimalPeriod_eq, hn]
  -- Conclude `P = card Q` by comparing cardinalities.
  have : P = Fintype.card Q := by
    rw [← hcardimg, hsurj, Finset.card_univ]
  exact this

/-- A single-cycle map of a finite type returns its basepoint to itself after
`Fintype.card Q` steps.  (Internally `Fintype.card Q = minimalPeriod T q0`.) -/
theorem isSingleCycleMap_iterate_card (hT : IsSingleCycleMap T) (q0 : Q) :
    T^[Fintype.card Q] q0 = q0 := by
  have hP : Function.minimalPeriod T q0 = Fintype.card Q :=
    isSingleCycleMap_minimalPeriod_eq_card T hT q0
  rw [← hP]
  exact Function.iterate_minimalPeriod

/-- For a single-cycle map of a finite type, every point is reached from the
basepoint within `Fintype.card Q` steps. -/
theorem isSingleCycleMap_orbit_cover (hT : IsSingleCycleMap T) (q0 : Q) :
    ∀ q : Q, ∃ k : Nat, k < Fintype.card Q ∧ T^[k] q0 = q := by
  intro q
  rcases hT.2 q0 q with ⟨n, hn⟩
  have hP : Function.minimalPeriod T q0 = Fintype.card Q :=
    isSingleCycleMap_minimalPeriod_eq_card T hT q0
  have hPpos : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨q0⟩
  refine ⟨n % Fintype.card Q, Nat.mod_lt _ hPpos, ?_⟩
  rw [← hP, Function.iterate_mod_minimalPeriod_eq, hn]

end BaseCycle

section Holonomy

-- The `Fintype Q` instance is genuinely used (via `Fintype.card Q`) in the proofs
-- of the holonomy lemmas, but only appears in the *types* of the `card`-indexed
-- declarations.  Suppress the stylistic `Fintype`-in-type nudge for this section.
set_option linter.unusedFintypeInType false

variable {Q Y : Type*}

/-- The **skew product** of a base map `T : Q → Q` with a fibre family
`A : Q → Equiv.Perm Y`:  `S (q, y) = (T q, A q y)`.  This is `skewProductMap` with
the fibre step `fun q y => A q y`. -/
def skewProductHolonomyMap (T : Q → Q) (A : Q → Equiv.Perm Y) :
    Q × Y → Q × Y :=
  skewProductMap T (fun q y => A q y)

@[simp] theorem skewProductHolonomyMap_apply (T : Q → Q) (A : Q → Equiv.Perm Y)
    (p : Q × Y) :
    skewProductHolonomyMap T A p = (T p.1, A p.1 p.2) := rfl

/-- The **holonomy** of the skew product around the `T`-cycle based at `q0`: the
ordered fold of the fibre permutations along the orbit
`q0, T q0, …, T^[N-1] q0` (with `N = Fintype.card Q`), namely

  `W_{q0} y = A (T^[N-1] q0) (⋯ (A (T q0) (A q0 y)) ⋯)`.

Concretely it is the fibre iterate `skewFiberIterate` of the skew-product step,
run for `Fintype.card Q` steps from `q0`.  This def is chosen precisely so that
`S^[N] (q0, y) = (q0, W_{q0} y)` holds (see `iterate_card_skewProductHolonomy`). -/
def skewHolonomy [Fintype Q] (T : Q → Q) (A : Q → Equiv.Perm Y) (q0 : Q) : Y → Y :=
  skewFiberIterate T (fun q y => A q y) (Fintype.card Q) q0

/-- Unfolding lemma: the holonomy is the section-return map of the skew product. -/
theorem skewHolonomy_eq_sectionReturn [Fintype Q]
    (T : Q → Q) (A : Q → Equiv.Perm Y) (q0 : Q) :
    skewHolonomy T A q0 =
      sectionReturn (skewProductHolonomyMap T A) q0 (Fintype.card Q) := by
  rw [skewHolonomy, skewProductHolonomyMap,
    sectionReturn_skewProductMap_eq_fiberIterate]

/-- **Crux identity** (`lem:skew-product-holonomy`, the period identity):
one period of the base returns to the fibre with the holonomy applied,

  `S^[N] (q0, y) = (q0, W_{q0} y)`,  where `N = Fintype.card Q`,

*provided* the base map returns, `T^[N] q0 = q0` (true when `T` is a single cycle,
but stated here from the bare return hypothesis to keep the identity general). -/
theorem iterate_card_skewProductHolonomy_of_return [Fintype Q]
    (T : Q → Q) (A : Q → Equiv.Perm Y) (q0 : Q)
    (hret : T^[Fintype.card Q] q0 = q0) (y : Y) :
    (skewProductHolonomyMap T A)^[Fintype.card Q] (q0, y) =
      (q0, skewHolonomy T A q0 y) := by
  rw [skewProductHolonomyMap, skewProductMap_iterate_eq_base_fiber]
  exact Prod.ext hret rfl

/-- The fibre step `fun y => A q y` is a bijection for every `q` (each `A q` is an
`Equiv`). -/
theorem skewProductHolonomy_fiber_bijective (A : Q → Equiv.Perm Y) (q : Q) :
    Function.Bijective (fun y => A q y) :=
  (A q).bijective

/-- The holonomy is a bijection (an iterated composite of bijective fibre steps). -/
theorem skewHolonomy_bijective [Fintype Q]
    (T : Q → Q) (A : Q → Equiv.Perm Y) (q0 : Q) :
    Function.Bijective (skewHolonomy T A q0) := by
  rw [skewHolonomy]
  exact skewFiberIterate_bijective T (fun q y => A q y)
    (fun q => (A q).bijective) (Fintype.card Q) q0

/-- **Skew-product holonomy lemma (forward direction).**
`lem:skew-product-holonomy`.

If `T` is a single cycle on the finite type `Q`, `A : Q → Equiv.Perm Y` a family of
fibre permutations, and the holonomy `skewHolonomy T A q0` around the base cycle is
a single cycle on `Y`, then the skew product `S (q, y) = (T q, A q y)` is a single
cycle on `Q × Y`. -/
theorem single_cycle_skewProduct_holonomy [Fintype Q]
    (T : Q → Q) (A : Q → Equiv.Perm Y) (q0 : Q)
    (hT : IsSingleCycleMap T)
    (hW : IsSingleCycleMap (skewHolonomy T A q0)) :
    IsSingleCycleMap (skewProductHolonomyMap T A) := by
  refine single_cycle_of_skewProduct_base_orbit_monodromy
    T (fun q y => A q y) q0 (Fintype.card Q)
    hT.1
    (fun q => (A q).bijective)
    (isSingleCycleMap_iterate_card T hT q0)
    (isSingleCycleMap_orbit_cover T hT q0)
    ?_
  -- The section-return monodromy of the skew product is exactly the holonomy.
  have hsec : sectionReturn (skewProductHolonomyMap T A) q0 (Fintype.card Q) =
      skewHolonomy T A q0 := (skewHolonomy_eq_sectionReturn T A q0).symm
  rw [show skewProductMap T (fun q y => A q y) = skewProductHolonomyMap T A from rfl,
    hsec]
  exact hW

/-- **Skew-product holonomy lemma (`iff`).**  For `T` a single cycle, the skew
product is a single cycle iff its holonomy is.  The reverse direction recovers the
holonomy as the section return of `S` and transports cyclicity back through it. -/
theorem single_cycle_skewProduct_holonomy_iff [Fintype Q]
    (T : Q → Q) (A : Q → Equiv.Perm Y) (q0 : Q)
    (hT : IsSingleCycleMap T) :
    IsSingleCycleMap (skewProductHolonomyMap T A) ↔
      IsSingleCycleMap (skewHolonomy T A q0) := by
  constructor
  · intro hS
    -- Reverse direction: pull single-cycleness of `S` back to the fibre `{q0}×Y`.
    refine ⟨skewHolonomy_bijective T A q0, ?_⟩
    intro y y'
    -- `S^[N·n] (q0, y) = (q0, W^[n] y)` by iterating the crux identity.
    have hret : T^[Fintype.card Q] q0 = q0 := isSingleCycleMap_iterate_card T hT q0
    have hreturn : ∀ z : Y,
        (skewProductHolonomyMap T A)^[Fintype.card Q] (q0, z) =
          (q0, skewHolonomy T A q0 z) :=
      fun z => iterate_card_skewProductHolonomy_of_return T A q0 hret z
    -- transitivity of `S` from `(q0,y)` to `(q0,y')`
    rcases hS.2 (q0, y) (q0, y') with ⟨n, hn⟩
    -- Decompose `n = N·a + r` with `r < N` and route through the section.
    -- Use the multiple-of-period identity: `S^[N·a] (q0,y) = (q0, W^[a] y)`.
    have hmul : ∀ a : Nat, ∀ z : Y,
        (skewProductHolonomyMap T A)^[a * Fintype.card Q] (q0, z) =
          (q0, (skewHolonomy T A q0)^[a] z) := by
      have := iterate_mul_base_of_periodic_return
        (skewProductHolonomyMap T A) (fun z : Y => (q0, z))
        (skewHolonomy T A q0) (Fintype.card Q) hreturn
      intro a z
      simpa using this a z
    -- The base coordinate of `S^[n] (q0,y)` is `T^[n] q0 = q0`, forcing
    -- `Fintype.card Q ∣ n` is NOT generally true; instead reduce via the fibre.
    -- We use that `(S^[n] (q0,y)).1 = T^[n] q0`. Since the result is `(q0, y')`,
    -- `T^[n] q0 = q0`, i.e. `n` is a multiple of `minimalPeriod = card`.
    have hbase : T^[n] q0 = q0 := by
      have : ((skewProductHolonomyMap T A)^[n] (q0, y)).1 = q0 := by
        rw [hn]
      rw [skewProductHolonomyMap, skewProductMap_fst_iterate] at this
      simpa using this
    -- `T^[n] q0 = q0` ⟹ `minimalPeriod T q0 ∣ n` ⟹ `card Q ∣ n`.
    have hdvd : Fintype.card Q ∣ n := by
      have hP : Function.minimalPeriod T q0 = Fintype.card Q :=
        isSingleCycleMap_minimalPeriod_eq_card T hT q0
      have : Function.minimalPeriod T q0 ∣ n :=
        Function.isPeriodicPt_iff_minimalPeriod_dvd.mp hbase
      rwa [hP] at this
    rcases hdvd with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have hroute := hmul a y
    rw [Nat.mul_comm] at ha
    rw [ha] at hn
    rw [hn] at hroute
    -- hroute : (q0, y') = (q0, W^[a] y)
    exact (Prod.ext_iff.mp hroute.symm).2
  · intro hW
    exact single_cycle_skewProduct_holonomy T A q0 hT hW

end Holonomy

/-! ## Additive corollary (`lem:unit-carry` / `lem:product-cycle-exponent`)

The special case `Y = ZMod m`, with each fibre permutation a translation
`A q = (· + γ q)`.  Then the holonomy is itself a translation by the total carry
`Σ_{x : Q} γ x` around the base cycle, and the skew product is a single cycle
exactly when that total carry is a unit. -/

section Additive

variable {Q : Type*} [Fintype Q] {m : Nat}

/-- For `T` a single cycle, the additive carry around the full base cycle equals the
sum of the per-point carries over all of `Q` (the orbit `i ↦ T^[i] q0` for
`i < card Q` is a bijection onto `Q`). -/
theorem skewFiberAdditiveCarry_card_eq_univ_sum_of_singleCycle
    (T : Q → Q) (γ : Q → ZMod m) (q0 : Q) (hT : IsSingleCycleMap T) :
    skewFiberAdditiveCarry T γ (Fintype.card Q) q0 = ∑ x : Q, γ x := by
  classical
  rw [skewFiberAdditiveCarry_eq_sum_range]
  -- Reindex the range sum along the orbit bijection `i ↦ T^[i] q0`.
  refine Finset.sum_bij (fun i _hi => T^[i] q0) (by intro i hi; simp) ?inj ?surj
    (fun i _hi => rfl)
  · -- injectivity on `range (card Q)` via `iterate_injOn_Iio_minimalPeriod`
    intro i hi j hj hij
    have hP : Function.minimalPeriod T q0 = Fintype.card Q :=
      isSingleCycleMap_minimalPeriod_eq_card T hT q0
    have hii : i ∈ Set.Iio (Function.minimalPeriod T q0) := by
      rw [hP]; simpa using Finset.mem_range.mp hi
    have hjj : j ∈ Set.Iio (Function.minimalPeriod T q0) := by
      rw [hP]; simpa using Finset.mem_range.mp hj
    exact Function.iterate_injOn_Iio_minimalPeriod hii hjj hij
  · -- surjectivity onto `univ` via the orbit cover
    intro x _hx
    rcases isSingleCycleMap_orbit_cover T hT q0 x with ⟨k, hk, hkx⟩
    exact ⟨k, Finset.mem_range.mpr hk, hkx⟩

/-- **Additive skew-product holonomy corollary.**  With fibre `ZMod m` and each
fibre permutation the translation `A q = (· + γ q)`, if `T` is a single cycle and
the total carry `Σ_x γ x` around the base cycle is a unit, then the skew product
`S (q, z) = (T q, z + γ q)` is a single cycle. -/
theorem single_cycle_skewProduct_additive_unit_sum [NeZero m]
    (T : Q → Q) (γ : Q → ZMod m) (q0 : Q)
    (hT : IsSingleCycleMap T)
    (hunit : IsUnit (∑ x : Q, γ x)) :
    IsSingleCycleMap
      (skewProductHolonomyMap T (fun q => Equiv.addRight (γ q))) := by
  -- The holonomy of the additive family is the translation by the total carry.
  have hWeq : skewHolonomy T (fun q => Equiv.addRight (γ q)) q0 =
      (fun z : ZMod m => z + ∑ x : Q, γ x) := by
    funext z
    rw [skewHolonomy]
    have hstep :
        (fun q (y : ZMod m) => (Equiv.addRight (γ q)) y) =
          (fun (b : Q) (y : ZMod m) => y + γ b) := by
      funext q y; rfl
    rw [hstep, skewFiberIterate_zmod_add,
      skewFiberAdditiveCarry_card_eq_univ_sum_of_singleCycle T γ q0 hT]
  refine single_cycle_skewProduct_holonomy T (fun q => Equiv.addRight (γ q)) q0 hT ?_
  rw [hWeq]
  exact zmod_add_single_cycle_of_unit hunit

end Additive

end Shared
