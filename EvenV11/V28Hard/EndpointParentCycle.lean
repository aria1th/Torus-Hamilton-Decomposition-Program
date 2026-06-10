import EvenV11.FinalTargetPredicateBridge
import EvenV11.V28Hard.CompletionTower
import EvenV11.V28Hard.EndpointPortRoom

/-!
# Hard slot H6 (E6a): parent-cycle extraction

`E6_DESIGN_20260610.md` §5.1.  From a bare parent payload
`FinalMarkedPayload b m` (whose target is `Nonempty (CayleyDecomposition b m)`)
and any parent color `c`, this file extracts a single `m^(b-1)`-cycle on the
height-zero section of the parent torus — without access to the parent's word.

* `S` is the coordinate-sum height; every Cayley color step adds one positive
  generator, so `S` increases by `1` per step (`S_step`, `S_iterate`).
* `ParentSection b m` is the zero-height section; it is chart-equivalent to
  the lane space `LaneZ b m` by dropping the last coordinate
  (`parentSectionEquiv`), hence has `m^(b-1)` points (`card_parentSection`).
* `parentReturn D c` is the `m`-fold color step restricted to the section;
  **E6a-1** (`parentReturn_singleCycle`) shows it is a single cycle, and
  **E6a-2** (`parentReturn_rankEquiv`) normalizes it to `+1` on
  `ZMod (m^(b-1))` via `CompletionTower.rankEquiv_of_singleCycle`.
* `parentCycleOfPayload` is the thin adapter extracting the decomposition
  from the payload by choice (the payload is a `Prop`; only the abstract
  cycle, never the parent schedule, is recoverable).
-/

namespace EvenV11
namespace V28Hard
namespace EndpointParentCycle

/-! ## Part A — the height functional -/

/-- Height of a torus vertex: the sum of its coordinates in `ZMod m`. -/
def S {b m : Nat} (x : Shared.TorusVertex b m) : ZMod m := ∑ i, x i

/-- A basis vector has height `1`. -/
theorem sum_torusBasis {d m : Nat} (i : Shared.TorusDirection d) :
    ∑ j, Shared.torusBasis d m i j = 1 := by
  simp [Shared.torusBasis]

/-- Every Cayley color step adds exactly one positive generator, so the
height increases by `1`. -/
theorem S_step {b m : Nat}
    (colorDir : Shared.TorusColor b → Shared.TorusVertex b m →
      Shared.TorusDirection b)
    (c : Shared.TorusColor b) (x : Shared.TorusVertex b m) :
    S (Shared.cayleyColorStep colorDir c x) = S x + 1 := by
  simp [S, Shared.cayleyColorStep, Finset.sum_add_distrib,
    Shared.torusBasis]

/-- Iterated height bookkeeping: `n` color steps raise the height by `n`. -/
theorem S_iterate {b m : Nat}
    (colorDir : Shared.TorusColor b → Shared.TorusVertex b m →
      Shared.TorusDirection b)
    (c : Shared.TorusColor b) (n : Nat) (x : Shared.TorusVertex b m) :
    S ((Shared.cayleyColorStep colorDir c)^[n] x) = S x + n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', S_step, ih]
      push_cast
      ring

/-! ## Part B — the zero-height section and its lane chart -/

/-- The zero-height section of the parent torus. -/
abbrev ParentSection (b m : Nat) :=
  {x : Shared.TorusVertex b m // S x = 0}

/-- Generic chart for a zero-sum tuple over `Fin (n+1)`: drop the last
coordinate; the inverse refills it as minus the sum of the others. -/
def zeroSumSnocEquiv (n m : Nat) :
    {x : Fin (n + 1) → ZMod m // ∑ i, x i = 0} ≃ (Fin n → ZMod m) where
  toFun x := Fin.init x.1
  invFun y :=
    ⟨Fin.snoc y (-(∑ j, y j)), by
      rw [Fin.sum_univ_castSucc]
      simp [Fin.snoc]⟩
  left_inv := by
    rintro ⟨x, hx⟩
    apply Subtype.ext
    have hlast : x (Fin.last n) = -(∑ j, Fin.init x j) := by
      rw [Fin.sum_univ_castSucc] at hx
      exact eq_neg_of_add_eq_zero_right hx
    calc
      Fin.snoc (Fin.init x) (-(∑ j, Fin.init x j))
          = Fin.snoc (Fin.init x) (x (Fin.last n)) := by rw [hlast]
      _ = x := Fin.snoc_init_self x
  right_inv := fun y => Fin.init_snoc _ _

/-- The zero-height section is chart-equivalent to the lane space
`LaneZ b m = Fin (b-1) → ZMod m`: drop the last coordinate, refill
`x_{b-1} := −(sum of the others)`. -/
def parentSectionEquiv {b m : Nat} (hb : 1 ≤ b) :
    ParentSection b m ≃ EndpointPortRoom.LaneZ b m :=
  ((Equiv.subtypeEquiv
      (Equiv.arrowCongr (finCongr (Nat.sub_add_cancel hb))
        (Equiv.refl (ZMod m)))
      (fun x' => by
        simp only [S, Equiv.arrowCongr_apply, Equiv.coe_refl,
          Function.comp_apply, id_eq]
        rw [Equiv.sum_comp (finCongr (Nat.sub_add_cancel hb)).symm
          x'])).symm).trans
    (zeroSumSnocEquiv (b - 1) m)

/-- The zero-height section has `m^(b-1)` points. -/
theorem card_parentSection {b m : Nat} [NeZero m] (hb : 1 ≤ b) :
    Nat.card (ParentSection b m) = m ^ (b - 1) := by
  rw [Nat.card_congr (parentSectionEquiv hb), Nat.card_eq_fintype_card,
    EndpointPortRoom.laneZ_card]

/-! ## Part C — the parent return and E6a-1/E6a-2 -/

/-- The parent return: `m` color steps, restricted to the zero-height
section (height `+ m = 0` mod `m`). -/
def parentReturn {b m : Nat} (D : Shared.CayleyDecomposition b m)
    (c : Shared.TorusColor b) (x : ParentSection b m) :
    ParentSection b m :=
  ⟨(Shared.cayleyColorStep D.colorDir c)^[m] x.1, by
    rw [S_iterate, x.2, ZMod.natCast_self, zero_add]⟩

/-- Iterates of the parent return are `k*m`-fold color steps upstairs. -/
theorem parentReturn_iterate_val {b m : Nat}
    (D : Shared.CayleyDecomposition b m) (c : Shared.TorusColor b)
    (k : Nat) (x : ParentSection b m) :
    ((parentReturn D c)^[k] x).1 =
      (Shared.cayleyColorStep D.colorDir c)^[k * m] x.1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply',
        show ((parentReturn D c) ((parentReturn D c)^[k] x)).1 =
            (Shared.cayleyColorStep D.colorDir c)^[m]
              ((parentReturn D c)^[k] x).1 from rfl,
        ih, ← Function.iterate_add_apply,
        show m + k * m = (k + 1) * m by ring]

/-- **Theorem (E6a-1).**  The parent return is a single
`m^(b-1)`-cycle on the zero-height section. -/
theorem parentReturn_singleCycle {b m : Nat} [NeZero m]
    (D : Shared.CayleyDecomposition b m) (c : Shared.TorusColor b) :
    Shared.IsSingleCycleMap (parentReturn D c) := by
  have hg : Shared.IsSingleCycleMap
      (Shared.cayleyColorStep D.colorDir c) := D.colorHamiltonian c
  have hgm : Function.Bijective
      ((Shared.cayleyColorStep D.colorDir c)^[m]) := hg.1.iterate m
  have hinj : Function.Injective (parentReturn D c) := fun x y hxy =>
    Subtype.ext (hgm.1 (congrArg Subtype.val hxy))
  refine ⟨Finite.injective_iff_bijective.mp hinj, fun x y => ?_⟩
  -- Transitivity upstairs gives `n`; heights force `m ∣ n`.
  obtain ⟨n, hn⟩ := hg.2 x.1 y.1
  have hmod : (n : ZMod m) = 0 := by
    have hS := S_iterate D.colorDir c n x.1
    rw [hn, x.2, y.2, zero_add] at hS
    exact hS.symm
  obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff n m).mp hmod
  exact ⟨k, Subtype.ext (by
    rw [parentReturn_iterate_val, show k * m = n by rw [hk, Nat.mul_comm],
      hn])⟩

/-- **Corollary (E6a-2).**  The parent return admits a `ZMod (m^(b-1))`
rank normalization stepping by `+1`. -/
theorem parentReturn_rankEquiv {b m : Nat} [NeZero m] (hb : 1 ≤ b)
    (D : Shared.CayleyDecomposition b m) (c : Shared.TorusColor b) :
    ∃ rank : ParentSection b m ≃ ZMod (m ^ (b - 1)),
      ∀ x, rank (parentReturn D c x) = rank x + 1 := by
  haveI : NeZero (m ^ (b - 1)) := ⟨pow_ne_zero _ (NeZero.ne m)⟩
  exact CompletionTower.rankEquiv_of_singleCycle (parentReturn D c)
    (parentReturn_singleCycle D c) (card_parentSection hb)

/-! ## Part D — thin adapter from the marked payload -/

/-- Extract a Cayley decomposition from the (propositional) payload by
choice.  Only the abstract decomposition is recoverable — never the
parent's word/schedule. -/
noncomputable def payloadDecomposition {b m : Nat}
    (payload : FinalMarkedPayload b m) :
    Shared.CayleyDecomposition b m :=
  Classical.choice
    (show Nonempty (Shared.CayleyDecomposition b m) from payload.target)

/-- The parent cycle extracted from a marked payload at color `c`. -/
noncomputable def parentCycleOfPayload {b m : Nat}
    (payload : FinalMarkedPayload b m) (c : Shared.TorusColor b) :
    ParentSection b m → ParentSection b m :=
  parentReturn (payloadDecomposition payload) c

/-- E6a-1 for the payload adapter. -/
theorem parentCycleOfPayload_singleCycle {b m : Nat} [NeZero m]
    (payload : FinalMarkedPayload b m) (c : Shared.TorusColor b) :
    Shared.IsSingleCycleMap (parentCycleOfPayload payload c) :=
  parentReturn_singleCycle (payloadDecomposition payload) c

/-- E6a-2 for the payload adapter. -/
theorem parentCycleOfPayload_rankEquiv {b m : Nat} [NeZero m] (hb : 1 ≤ b)
    (payload : FinalMarkedPayload b m) (c : Shared.TorusColor b) :
    ∃ rank : ParentSection b m ≃ ZMod (m ^ (b - 1)),
      ∀ x, rank (parentCycleOfPayload payload c x) = rank x + 1 :=
  parentReturn_rankEquiv hb (payloadDecomposition payload) c

/-- Existence form for downstream (E6b) consumption: the bare payload
yields a single-cycle parent return on the zero-height section. -/
theorem exists_parentCycle_of_payload {b m : Nat} [NeZero m]
    (payload : FinalMarkedPayload b m) (c : Shared.TorusColor b) :
    ∃ P : ParentSection b m → ParentSection b m,
      Shared.IsSingleCycleMap P :=
  ⟨parentCycleOfPayload payload c,
    parentCycleOfPayload_singleCycle payload c⟩

end EndpointParentCycle
end V28Hard
end EvenV11
