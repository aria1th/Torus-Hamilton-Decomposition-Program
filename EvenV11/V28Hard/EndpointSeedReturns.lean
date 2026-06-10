import EvenV11.UnitCarry
import EvenV11.V28Hard.CompletionTower

/-!
# Hard slot H6 (E6b): abstract endpoint seed returns

`E6_DESIGN_20260610.md` §5.2–§5.4.  The paper's ledger models for the
child endpoint colors are proved single-cycle over abstract carriers:
`T : Q → Q` ranked by `ZMod NQ`, `P : Y → Y` ranked by `ZMod NY` (from
E6a/`rankEquiv_of_singleCycle`), and a crossing site `q₀ : Q`.

* **§5.2 active cores** — `activeT` (paper `t_i`: the parent return `P`
  fires exactly on the crossing fiber `{q = q₀}`) and `activeD` (paper
  `d_{i+1}`: `P` fires off the crossing fiber).  **E6b-1**
  (`activeT_singleCycle`) conjugates by the fiber rank chart into
  `additiveSkewMap T (pointCarry q₀ 1)` and closes with
  `pointCarrySingleCycle`.  **E6b-2** (`activeD_singleCycle`) lands on
  the complement-singleton exponent; the concrete corollary
  `activeD_singleCycle_square` at `NQ = m * m`, `NY = m ^ (b - 1)`
  closes with `complementSingletonSquareProductExponentSingleCycle` —
  the paper's `m² − 1` unit check, taken in `ZMod (m ^ (b - 1))`, never
  in `ZMod m` (`PAPER_NUMERIC_AUDIT_20260609.md` §4).
* **§5.3 tower attachment** — **E6b-3** `seedTower_singleCycle`
  re-exposes `CompletionTower.towerMap_singleCycle` for any single-cycle
  seed; instantiated for the two active cores over `Q × Y` via the card
  fact `Nat.card (Q × Y) = NQ * NY ≠ 0`.
* **§5.4 μ-class** — **E6b-4 (L-MONO)** `crossing_skew_singleCycle`:
  `(ζ, q) ↦ (ζ + 1, if ζ = ζ₀ then F q else q)` is a single cycle.  No
  new machinery: with base and fiber roles swapped relative to E6b-1,
  the map conjugates (through a fiber rank from
  `rankEquiv_of_singleCycle_card`) to
  `additiveSkewMap (· + 1) (pointCarry ζ₀ 1)`, whose base rank is
  `Equiv.refl (ZMod m)`.  `muSeed` names the special case and gets its
  tower attachment corollary.

Site plumbing connecting `EndpointPortRoom.EndpointRowList` completion
sites to tower certificate sites is E6c bookkeeping and deliberately not
included here (design §5.3, §7).
-/

namespace EvenV11
namespace V28Hard
namespace EndpointSeedReturns

/-! ## Part A — active cores (design §5.2) -/

/-- Paper `t_i` ledger model: the terminal return `T` always steps; the
parent return `P` fires exactly on the crossing fiber `{q = q₀}`. -/
def activeT {Q Y : Type*} [DecidableEq Q]
    (T : Q → Q) (P : Y → Y) (q₀ : Q) : Q × Y → Q × Y :=
  fun (q, y) => (T q, if q = q₀ then P y else y)

/-- Paper `d_{i+1}` ledger model: the terminal return `T` always steps;
the parent return `P` fires off the crossing fiber. -/
def activeD {Q Y : Type*} [DecidableEq Q]
    (T : Q → Q) (P : Y → Y) (q₀ : Q) : Q × Y → Q × Y :=
  fun (q, y) => (T q, if q = q₀ then y else P y)

/-- Conjugating `activeT` by the fiber rank chart gives the one-point
unit-carry additive skew map at the crossing site: on the crossing,
`rankP (P y) = rankP y + 1`; off it, `rankP y` is unchanged. -/
theorem activeT_conj {Q Y : Type*} [DecidableEq Q] {NY : Nat}
    (T : Q → Q) (P : Y → Y) (q₀ : Q) (rankP : Y ≃ ZMod NY)
    (hP : ∀ y, rankP (P y) = rankP y + 1) (x : Q × ZMod NY) :
    (Equiv.prodCongr (Equiv.refl Q) rankP.symm).symm
        (activeT T P q₀ (Equiv.prodCongr (Equiv.refl Q) rankP.symm x)) =
      additiveSkewMap T (pointCarry q₀ (1 : ZMod NY)) x := by
  rcases x with ⟨q, r⟩
  by_cases hq : q = q₀
  · simp [activeT, Shared.skewProductMap, pointCarry, hq, hP]
  · simp [activeT, Shared.skewProductMap, pointCarry, hq]

/-- **Theorem (E6b-1).**  The `t_i` ledger model `activeT` is a single
cycle: conjugate into `additiveSkewMap T (pointCarry q₀ 1)` and apply
`pointCarrySingleCycle` (total carry `1`, a unit of `ZMod NY`). -/
theorem activeT_singleCycle {Q Y : Type*} [Finite Q] [DecidableEq Q]
    {NQ NY : Nat} [NeZero NQ] [NeZero NY]
    (T : Q → Q) (rankT : Q ≃ ZMod NQ)
    (hT : ∀ q, rankT (T q) = rankT q + 1)
    (P : Y → Y) (rankP : Y ≃ ZMod NY)
    (hP : ∀ y, rankP (P y) = rankP y + 1) (q₀ : Q) :
    Shared.IsSingleCycleMap (activeT T P q₀) :=
  Shared.single_cycle_of_equiv_conj
    (Equiv.prodCongr (Equiv.refl Q) rankP.symm)
    (activeT T P q₀)
    (additiveSkewMap T (pointCarry q₀ (1 : ZMod NY)))
    (pointCarrySingleCycle T rankT (rankT.symm 0) q₀ (1 : ZMod NY)
      hT isUnit_one)
    (activeT_conj T P q₀ rankP hP)

/-- **Corollary (E6b-1, concrete).**  E6b-1 at the spec instances
`NQ = m * m` (terminal A₂ block) and `NY = m ^ (b - 1)` (parent
section). -/
theorem activeT_singleCycle_square {Q Y : Type*} [Finite Q]
    [DecidableEq Q] {m b : Nat} [NeZero m]
    (T : Q → Q) (rankT : Q ≃ ZMod (m * m))
    (hT : ∀ q, rankT (T q) = rankT q + 1)
    (P : Y → Y) (rankP : Y ≃ ZMod (m ^ (b - 1)))
    (hP : ∀ y, rankP (P y) = rankP y + 1) (q₀ : Q) :
    Shared.IsSingleCycleMap (activeT T P q₀) :=
  haveI : NeZero (m * m) := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne m)⟩
  haveI : NeZero (m ^ (b - 1)) := ⟨pow_ne_zero _ (NeZero.ne m)⟩
  activeT_singleCycle T rankT hT P rankP hP q₀

/-- Conjugating `activeD` by the fiber rank chart gives the
complement-singleton product-exponent map: carry `0` on the crossing
fiber, carry `1` everywhere else. -/
theorem activeD_conj {Q Y : Type*} [DecidableEq Q] {NY : Nat}
    (T : Q → Q) (P : Y → Y) (q₀ : Q) (rankP : Y ≃ ZMod NY)
    (hP : ∀ y, rankP (P y) = rankP y + 1) (x : Q × ZMod NY) :
    (Equiv.prodCongr (Equiv.refl Q) rankP.symm).symm
        (activeD T P q₀ (Equiv.prodCongr (Equiv.refl Q) rankP.symm x)) =
      productExponentMap T
        (fun q => if q = q₀ then (0 : ZMod NY) else 1) x := by
  rcases x with ⟨q, r⟩
  by_cases hq : q = q₀
  · simp [activeD, Shared.skewProductMap, hq]
  · simp [activeD, Shared.skewProductMap, hq, hP]

/-- **Theorem (E6b-2, abstract).**  The `d_{i+1}` ledger model `activeD`
is a single cycle whenever the complement carry total `NQ − 1` is a unit
of `ZMod NY`.  The spec instance of the unit hypothesis is the
`m² − 1` arithmetic of `activeD_singleCycle_square`. -/
theorem activeD_singleCycle {Q Y : Type*} [Finite Q] [DecidableEq Q]
    {NQ NY : Nat} [NeZero NQ] [NeZero NY]
    (T : Q → Q) (rankT : Q ≃ ZMod NQ)
    (hT : ∀ q, rankT (T q) = rankT q + 1)
    (P : Y → Y) (rankP : Y ≃ ZMod NY)
    (hP : ∀ y, rankP (P y) = rankP y + 1) (q₀ : Q)
    (hunit : IsUnit ((NQ - 1 : Nat) : ZMod NY)) :
    Shared.IsSingleCycleMap (activeD T P q₀) := by
  letI : Fintype Q := Fintype.ofFinite Q
  have hcard : Fintype.card Q = NQ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr rankT, Nat.card_zmod]
  refine Shared.single_cycle_of_equiv_conj
    (Equiv.prodCongr (Equiv.refl Q) rankP.symm)
    (activeD T P q₀)
    (productExponentMap T
      (fun q => if q = q₀ then (0 : ZMod NY) else 1))
    (complementSingletonProductExponentSingleCycle T rankT
      (rankT.symm 0) q₀ hT ?_)
    (activeD_conj T P q₀ rankP hP)
  rw [complementSingletonExponentSum q₀, hcard]
  exact hunit

/-- **Corollary (E6b-2, concrete).**  E6b-2 at the spec instances
`NQ = m * m`, `NY = m ^ (b - 1)`, `k := b − 1`, closed by
`complementSingletonSquareProductExponentSingleCycle`.  Audit trap
honored: the `m² − 1` unit lives in `ZMod (m ^ (b - 1))`, never in
`ZMod m`. -/
theorem activeD_singleCycle_square {Q Y : Type*} [Finite Q]
    [DecidableEq Q] {m b : Nat} [NeZero m]
    (T : Q → Q) (rankT : Q ≃ ZMod (m * m))
    (hT : ∀ q, rankT (T q) = rankT q + 1)
    (P : Y → Y) (rankP : Y ≃ ZMod (m ^ (b - 1)))
    (hP : ∀ y, rankP (P y) = rankP y + 1) (q₀ : Q) :
    Shared.IsSingleCycleMap (activeD T P q₀) := by
  haveI : NeZero (m * m) := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne m)⟩
  letI : Fintype Q := Fintype.ofFinite Q
  have hcard : Fintype.card Q = m * m := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr rankT, Nat.card_zmod]
  exact Shared.single_cycle_of_equiv_conj
    (Equiv.prodCongr (Equiv.refl Q) rankP.symm)
    (activeD T P q₀)
    (productExponentMap T
      (fun q => if q = q₀ then (0 : ZMod (m ^ (b - 1))) else 1))
    (complementSingletonSquareProductExponentSingleCycle
      (m := m) (k := b - 1) T rankT (rankT.symm 0) q₀ hT hcard)
    (activeD_conj T P q₀ rankP hP)

/-! ## Part B — tower attachment (design §5.3) -/

/-- **Theorem (E6b-3, generic).**  Any single-cycle seed on a finite base
of nonzero cardinality lifts through any completion tower.  This is
`CompletionTower.towerMap_singleCycle` re-exposed under the seed-return
naming. -/
theorem seedTower_singleCycle {B Coord : Type*} [Finite B]
    {mz r : Nat} [NeZero mz] [NeZero (Nat.card B)]
    (S : B → B) (hS : Shared.IsSingleCycleMap S)
    (Tw : CompletionTower.CompletionTower B Coord mz r) :
    Shared.IsSingleCycleMap (CompletionTower.towerMap S Tw) :=
  CompletionTower.towerMap_singleCycle S Tw hS

/-- Card bookkeeping for the active cores: the base `Q × Y` has
`NQ * NY` points. -/
theorem card_activeBase {Q Y : Type*} {NQ NY : Nat}
    (rankT : Q ≃ ZMod NQ) (rankP : Y ≃ ZMod NY) :
    Nat.card (Q × Y) = NQ * NY := by
  rw [Nat.card_prod, Nat.card_congr rankT, Nat.card_congr rankP,
    Nat.card_zmod, Nat.card_zmod]

/-- `NeZero` packaging of `card_activeBase`. -/
theorem card_activeBase_neZero {Q Y : Type*} {NQ NY : Nat}
    [NeZero NQ] [NeZero NY]
    (rankT : Q ≃ ZMod NQ) (rankP : Y ≃ ZMod NY) :
    NeZero (Nat.card (Q × Y)) :=
  ⟨by
    rw [card_activeBase rankT rankP]
    exact mul_ne_zero (NeZero.ne NQ) (NeZero.ne NY)⟩

/-- **Corollary (E6b-3 for `activeT`).**  The `t_i` seed model carries
any completion tower over `Q × Y` to a single cycle. -/
theorem activeT_towerMap_singleCycle {Q Y Coord : Type*}
    [Finite Q] [Finite Y] [DecidableEq Q]
    {NQ NY mz r : Nat} [NeZero NQ] [NeZero NY] [NeZero mz]
    (T : Q → Q) (rankT : Q ≃ ZMod NQ)
    (hT : ∀ q, rankT (T q) = rankT q + 1)
    (P : Y → Y) (rankP : Y ≃ ZMod NY)
    (hP : ∀ y, rankP (P y) = rankP y + 1) (q₀ : Q)
    (Tw : CompletionTower.CompletionTower (Q × Y) Coord mz r) :
    Shared.IsSingleCycleMap
      (CompletionTower.towerMap (activeT T P q₀) Tw) :=
  haveI := card_activeBase_neZero rankT rankP
  seedTower_singleCycle (activeT T P q₀)
    (activeT_singleCycle T rankT hT P rankP hP q₀) Tw

/-- **Corollary (E6b-3 for `activeD`).**  The `d_{i+1}` seed model
carries any completion tower over `Q × Y` to a single cycle, under the
abstract `NQ − 1` unit hypothesis. -/
theorem activeD_towerMap_singleCycle {Q Y Coord : Type*}
    [Finite Q] [Finite Y] [DecidableEq Q]
    {NQ NY mz r : Nat} [NeZero NQ] [NeZero NY] [NeZero mz]
    (T : Q → Q) (rankT : Q ≃ ZMod NQ)
    (hT : ∀ q, rankT (T q) = rankT q + 1)
    (P : Y → Y) (rankP : Y ≃ ZMod NY)
    (hP : ∀ y, rankP (P y) = rankP y + 1) (q₀ : Q)
    (hunit : IsUnit ((NQ - 1 : Nat) : ZMod NY))
    (Tw : CompletionTower.CompletionTower (Q × Y) Coord mz r) :
    Shared.IsSingleCycleMap
      (CompletionTower.towerMap (activeD T P q₀) Tw) :=
  haveI := card_activeBase_neZero rankT rankP
  seedTower_singleCycle (activeD T P q₀)
    (activeD_singleCycle T rankT hT P rankP hP q₀ hunit) Tw

/-! ## Part C — μ-class seed and L-MONO (design §5.4) -/

/-- **Lemma (E6b-4, L-MONO).**  One full fiber return per base circuit:
if `F` is a single cycle on `Q`, then
`(ζ, q) ↦ (ζ + 1, if ζ = ζ₀ then F q else q)` is a single cycle on
`ZMod m × Q`.  With base and fiber roles swapped relative to E6b-1 this
is again the one-point unit-carry pattern: ranking the fiber by
`rankEquiv_of_singleCycle_card`, the map conjugates to
`additiveSkewMap (· + 1) (pointCarry ζ₀ 1)`, and `pointCarrySingleCycle`
applies with base rank `Equiv.refl (ZMod m)`. -/
theorem crossing_skew_singleCycle {Q : Type*} [Finite Q] {m : Nat}
    [NeZero m] (F : Q → Q) (hF : Shared.IsSingleCycleMap F)
    (ζ₀ : ZMod m) :
    Shared.IsSingleCycleMap
      (fun zq : ZMod m × Q =>
        (zq.1 + 1, if zq.1 = ζ₀ then F zq.2 else zq.2)) := by
  rcases isEmpty_or_nonempty Q with hQ | hQ
  · haveI : IsEmpty (ZMod m × Q) := ⟨fun x => hQ.false x.2⟩
    exact ⟨⟨fun a b _ => Subsingleton.elim a b,
        fun y => (IsEmpty.false y).elim⟩,
      fun x => (IsEmpty.false x).elim⟩
  · haveI : NeZero (Nat.card Q) :=
      ⟨Nat.card_ne_zero.mpr ⟨hQ, inferInstance⟩⟩
    obtain ⟨rankF, hrankF⟩ :=
      CompletionTower.rankEquiv_of_singleCycle_card F hF
    refine Shared.single_cycle_of_equiv_conj
      (Equiv.prodCongr (Equiv.refl (ZMod m)) rankF.symm) _
      (additiveSkewMap (fun ζ : ZMod m => ζ + 1)
        (pointCarry ζ₀ (1 : ZMod (Nat.card Q))))
      (pointCarrySingleCycle (fun ζ : ZMod m => ζ + 1)
        (Equiv.refl (ZMod m)) 0 ζ₀ (1 : ZMod (Nat.card Q))
        (fun _ => rfl) isUnit_one) ?_
    rintro ⟨ζ, ρ⟩
    by_cases hζ : ζ = ζ₀
    · simp [Shared.skewProductMap, pointCarry, hζ, hrankF]
    · simp [Shared.skewProductMap, pointCarry, hζ]

/-- μ-class seed model (design §5.4, the D5(4) §11 `P₀`-shape): the base
lane coordinate steps `+1`; the fiber receives a full D3 return `F`
exactly on the crossing fiber `{ζ = ζ₀}`. -/
def muSeed {Q : Type*} {m : Nat} (F : Q → Q) (ζ₀ : ZMod m) :
    ZMod m × Q → ZMod m × Q :=
  fun zq => (zq.1 + 1, if zq.1 = ζ₀ then F zq.2 else zq.2)

/-- The μ-class seed is a single cycle (named special case of
L-MONO). -/
theorem muSeed_singleCycle {Q : Type*} [Finite Q] {m : Nat} [NeZero m]
    (F : Q → Q) (hF : Shared.IsSingleCycleMap F) (ζ₀ : ZMod m) :
    Shared.IsSingleCycleMap (muSeed F ζ₀) :=
  crossing_skew_singleCycle F hF ζ₀

/-- **Corollary (E6b-3 for `muSeed`).**  The μ-class seed carries any
completion tower over `ZMod m × Q` to a single cycle. -/
theorem muSeed_towerMap_singleCycle {Q Coord : Type*} [Finite Q]
    [Nonempty Q] {m mz r : Nat} [NeZero m] [NeZero mz]
    (F : Q → Q) (hF : Shared.IsSingleCycleMap F) (ζ₀ : ZMod m)
    (Tw : CompletionTower.CompletionTower (ZMod m × Q) Coord mz r) :
    Shared.IsSingleCycleMap
      (CompletionTower.towerMap (muSeed F ζ₀) Tw) := by
  haveI : NeZero (Nat.card (ZMod m × Q)) := ⟨by
    rw [Nat.card_prod, Nat.card_zmod]
    exact mul_ne_zero (NeZero.ne m)
      (Nat.card_ne_zero.mpr ⟨‹Nonempty Q›, inferInstance⟩)⟩
  exact seedTower_singleCycle (muSeed F ζ₀)
    (muSeed_singleCycle F hF ζ₀) Tw

end EndpointSeedReturns
end V28Hard
end EvenV11
