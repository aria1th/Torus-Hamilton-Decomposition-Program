# GPT-5.5 Pro Active Hall-Slack Response

Date: 2026-05-03.

Response id: `resp_01bc2f30d606b77c0069f781eded40819ca33fc85820d0d3c4`.

Note: request prompt used the earlier odd-dimension wording; read this against the corrected odd-core plus D2/product wrapper architecture.

Below is a pragmatic Lean architecture for the active Hall-slack branch.  I would keep the polyhedral/Hall material completely separate from the torus construction, and make the torus construction consume an explicit active-symboling certificate.

---

## 0. Lean-friendly restatement

Use an explicit `T` with `d = b + T` instead of constantly rewriting `T = d - b`.

```lean
theorem BaseTail.hallSlackBranch_add
    {m b d T : ℕ} [NeZero m]
    (hm3 : 3 ≤ m) (hm_odd : Odd m)
    (hd_odd : Odd d)
    (hbpos : 0 < b)
    (hd_eq : d = b + T)
    (Hb : Shared.CayleyHamiltonDecomposition b m)
    (k : Fin b → ℕ)
    (hk_sum : (∑ j : Fin b, k j) = d)
    (hk_units : ∀ j : Fin b, PositiveUnitSum m (k j))
    (hTb : T > b)
    (hbig : m^b > m * d * T) :
    Shared.CayleyHamiltonDecomposition d m
```

Then provide a wrapper matching the manuscript:

```lean
theorem BaseTail.hallSlackBranch_sub
    {m b d : ℕ} [NeZero m]
    (hm3 : 3 ≤ m) (hm_odd : Odd m)
    (hd_odd : Odd d)
    (hmd : m < d)
    (hbpos : 0 < b) (hbd : b < d)
    (Hb : Shared.CayleyHamiltonDecomposition b m)
    (k : Fin b → ℕ)
    (hk_sum : (∑ j : Fin b, k j) = d)
    (hk_units : ∀ j : Fin b, PositiveUnitSum m (k j))
    (hTb : d - b > b)
    (hbig : m^b > m * d * (d - b)) :
    Shared.CayleyHamiltonDecomposition d m
```

The additive version is much easier to use with `omega`.

---

## 1. Core active Hall API

Put this in `ActiveHall/Basic.lean`.

```lean
namespace ActiveHall

open scoped BigOperators

variable {T : ℕ}
variable {X C : Type*}
variable [Fintype X] [DecidableEq X]
variable [Fintype C] [DecidableEq C]

structure Incidence (T : ℕ) (X C : Type*)
    [Fintype X] [Fintype C] [DecidableEq C] where
  active : X → Finset C
  active_card : ∀ x : X, (active x).card = T

namespace Incidence

def colorDegree (I : Incidence T X C) (c : C) : ℕ :=
  (Finset.univ.filter fun x : X => c ∈ I.active x).card

def cutCap (I : Incidence T X C)
    (U : Finset C) (S : Finset (Fin T)) : ℕ :=
  ∑ x : X, min ((I.active x ∩ U).card) S.card

def matrixCut (M : C → Fin T → ℕ)
    (U : Finset C) (S : Finset (Fin T)) : ℕ :=
  ∑ c in U, ∑ σ in S, M c σ

def RowSumOk (I : Incidence T X C) (M : C → Fin T → ℕ) : Prop :=
  ∀ c : C, (∑ σ : Fin T, M c σ) = I.colorDegree c

def ColSumOk (I : Incidence T X C) (M : C → Fin T → ℕ) : Prop :=
  ∀ σ : Fin T, (∑ c : C, M c σ) = Fintype.card X

def HallCuts (I : Incidence T X C) (M : C → Fin T → ℕ) : Prop :=
  ∀ U : Finset C, ∀ S : Finset (Fin T),
    matrixCut M U S ≤ I.cutCap U S

noncomputable def bary (I : Incidence T X C) (c : C) (_ : Fin T) : ℚ :=
  (I.colorDegree c : ℚ) / (T : ℚ)

def qCut (I : Incidence T X C) (Q : C → Fin T → ℚ)
    (U : Finset C) (S : Finset (Fin T)) : ℚ :=
  ∑ c in U, ∑ σ in S, Q c σ

def qSlack (I : Incidence T X C) (Q : C → Fin T → ℚ)
    (U : Finset C) (S : Finset (Fin T)) : ℚ :=
  (I.cutCap U S : ℚ) - I.qCut Q U S

end Incidence

structure CountMatrix (I : Incidence T X C) where
  val : C → Fin T → ℕ
  row_sum : I.RowSumOk val
  col_sum : I.ColSumOk val
  hall : I.HallCuts val
```

Symbolings should store a bijection at each base vertex.  This avoids repeatedly proving local bijectivity.

```lean
structure Symboling (I : Incidence T X C) where
  symEquiv : ∀ x : X, {c : C // c ∈ I.active x} ≃ Fin T

namespace Symboling

def symbol {I : Incidence T X C} (Φ : Symboling I)
    {x : X} {c : C} (hc : c ∈ I.active x) : Fin T :=
  Φ.symEquiv x ⟨c, hc⟩

noncomputable def count {I : Incidence T X C} (Φ : Symboling I)
    (c : C) (σ : Fin T) : ℕ :=
  (Finset.univ.filter fun x : X =>
    if hc : c ∈ I.active x then Φ.symbol hc = σ else False).card

def Realizes {I : Incidence T X C} (Φ : Symboling I)
    (M : C → Fin T → ℕ) : Prop :=
  ∀ c σ, Φ.count c σ = M c σ

end Symboling
```

Useful direct lemmas:

```lean
theorem Incidence.sum_colorDegree (I : Incidence T X C) :
    (∑ c : C, I.colorDegree c) = T * Fintype.card X := by
  -- direct double-counting

theorem Incidence.sum_colorDegree_on
    (I : Incidence T X C) (U : Finset C) :
    (∑ c in U, I.colorDegree c)
      = ∑ x : X, (I.active x ∩ U).card := by
  -- restricted double-counting

theorem Symboling.count_row_sum {I : Incidence T X C}
    (Φ : Symboling I) :
    I.RowSumOk Φ.count := by
  -- each active edge at color c gets exactly one symbol

theorem Symboling.count_col_sum {I : Incidence T X C}
    (Φ : Symboling I) :
    I.ColSumOk Φ.count := by
  -- at each x, every symbol appears once
```

---

## 2. Residue API

Put this in `ActiveHall/Residues.lean`.

Use `Fin T` as the symbol type.  Symbol `0` is `val = 0`, symbol `Delta` is `val = 1`, numeric symbols are `val ≥ 2`.

```lean
namespace ActiveHall

structure ResidueSpec (m T : ℕ) (C : Type*) [Fintype C] where
  u : C → ZMod m
  unit_u : ∀ c, IsUnit (u c)
  sum_u : (∑ c : C, u c) = 0

namespace ResidueSpec

def target {m T : ℕ} {C : Type*} [Fintype C]
    (R : ResidueSpec m T C) (c : C) (σ : Fin T) : ZMod m :=
  if σ.val = 0 then R.u c
  else if σ.val = 1 then - R.u c
  else 0

end ResidueSpec

def HasResidues {m T : ℕ} {C : Type*} [Fintype C]
    (M : C → Fin T → ℕ) (R : ResidueSpec m T C) : Prop :=
  ∀ c σ, (M c σ : ZMod m) = R.target c σ

def Symboling.HasResidues {m T : ℕ} {X C : Type*}
    [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    {I : Incidence T X C}
    (Φ : Symboling I) (R : ResidueSpec m T C) : Prop :=
  ∀ c σ, (Φ.count c σ : ZMod m) = R.target c σ
```

Residue compatibility lemmas:

```lean
theorem ResidueSpec.sum_target_symbols
    {m T : ℕ} {C : Type*} [Fintype C]
    (R : ResidueSpec m T C) (hT2 : 2 ≤ T) (c : C) :
    (∑ σ : Fin T, R.target c σ) = 0 := by
  -- exactly one symbol with val 0 and one with val 1

theorem ResidueSpec.sum_target_colors
    {m T : ℕ} {C : Type*} [Fintype C]
    (R : ResidueSpec m T C) (σ : Fin T) :
    (∑ c : C, R.target c σ) = 0 := by
  -- zero column uses sum_u, Delta uses -sum_u, numeric is zero
```

Odd `d` residue pattern:

```lean
noncomputable def oddResidueSpec
    {m d T : ℕ} [NeZero m]
    (hm_odd : Odd m) (hd_odd : Odd d) (hd3 : 3 ≤ d)
    (C : Type*) [Fintype C] [DecidableEq C]
    (hC : Fintype.card C = d) :
    ResidueSpec m T C := by
  -- choose equivalence C ≃ Fin d
  -- assign [1, 1, -2] and then pairs [1, -1]
  -- prove all are units in ZMod m
  -- prove total sum is zero
```

This is direct mathlib work.  The only mildly annoying piece is proving `-2` is a unit in `ZMod m` from `Odd m`; use `ZMod.isUnit_iff_coprime` or `ZMod.unitOfCoprime`.

---

## 3. Hall slack from mixed vertices

Put this in `ActiveHall/Slack.lean`.

The manuscript’s slack lower bound is best formalized through a “mixed vertex” expansion statement.

```lean
namespace ActiveHall

def NontrivialCut {T : ℕ} {C : Type*} [Fintype C]
    (U : Finset C) (S : Finset (Fin T)) : Prop :=
  U.Nonempty ∧ U.card < Fintype.card C ∧ S.Nonempty ∧ S.card < T

namespace Incidence

def mixedCount (I : Incidence T X C) (U : Finset C) : ℕ :=
  (Finset.univ.filter fun x : X =>
    0 < (I.active x ∩ U).card ∧ (I.active x ∩ U).card < T).card

end Incidence

structure MixedExpansion (m b : ℕ) (I : Incidence T X C) : Prop where
  lower :
    ∀ U : Finset C,
      U.Nonempty →
      U.card < Fintype.card C →
      m^b ≤ I.mixedCount U

structure HallSlackBound (m b : ℕ) (I : Incidence T X C) : Prop where
  lower :
    ∀ U : Finset C, ∀ S : Finset (Fin T),
      NontrivialCut U S →
        ((m^b : ℚ) / (T : ℚ)) *
          (min S.card (T - S.card) : ℚ)
        ≤ I.qSlack I.bary U S
```

Generic barycenter lemmas:

```lean
theorem bary_mem_hall
    (I : Incidence T X C) (hTpos : 0 < T) :
    ∀ U : Finset C, ∀ S : Finset (Fin T),
      I.qCut I.bary U S ≤ (I.cutCap U S : ℚ) := by
  -- reduce to pointwise:
  -- (S.card / T) * a ≤ min a S.card, where 0 ≤ a ≤ T

theorem hallSlackBound_of_mixedExpansion
    (I : Incidence T X C) (hTpos : 0 < T)
    (hMix : MixedExpansion m b I) :
    HallSlackBound m b I := by
  -- Write slack as sum over x of
  --   min a_x s - (s/T) * a_x
  -- where a_x = |A(x) ∩ U| and s = |S|.
  -- At mixed x, 0 < a_x < T, contribution ≥ min(s,T-s)/T.
  -- hMix gives at least m^b mixed x.
```

This is a good Lean target: no max-flow, no TU, only finite sums and rational inequalities.

For the base-tail incidence, prove:

```lean
theorem BaseTail.activeIncidence_mixedExpansion
    -- parameters omitted
    (hTb : T > b) :
    ActiveHall.MixedExpansion m b I := by
  -- use root-flat / skew-product / single-cycle lemmas
```

This is where the existing root-flat/skew-product/single-cycle infrastructure should enter.

---

## 4. Rounding and Hoffman realization interfaces

Put this in `ActiveHall/Rounding.lean` and `ActiveHall/Hoffman.lean`.

First isolate the controlled residue rounding as a precise theorem.  I recommend proving Hall preservation from closeness directly, but temporarily axiomatizing only the modular transportation rounding.

```lean
namespace ActiveHall

def CloseToBary (m : ℕ) (I : Incidence T X C)
    (M : C → Fin T → ℕ) : Prop :=
  ∀ c σ, |((M c σ : ℚ) - I.bary c σ)| ≤ (m : ℚ)

/-- Modular transportation rounding.  This is the hard rounding theorem. -/
axiom residue_transport_rounding_close
    {m T : ℕ} [NeZero m]
    {X C : Type*} [Fintype X] [DecidableEq X]
    [Fintype C] [DecidableEq C]
    (I : Incidence T X C) (R : ResidueSpec m T C)
    (hTpos : 0 < T)
    (hrowCompat :
      ∀ c : C, (I.colorDegree c : ZMod m)
        = ∑ σ : Fin T, R.target c σ)
    (hcolCompat :
      ∀ σ : Fin T, (Fintype.card X : ZMod m)
        = ∑ c : C, R.target c σ)
    (hRoom : ∀ c σ, (m : ℚ) ≤ I.bary c σ) :
    ∃ M : C → Fin T → ℕ,
      I.RowSumOk M ∧
      I.ColSumOk M ∧
      HasResidues M R ∧
      CloseToBary m I M
```

Then prove the Hall inequalities from slack plus closeness.

```lean
theorem hallCuts_of_closeToBary
    {m b d T : ℕ}
    (I : Incidence T X C)
    (hTpos : 0 < T)
    (hC : Fintype.card C = d)
    (hSlack : HallSlackBound m b I)
    (hbig : m^b > m * d * T)
    {M : C → Fin T → ℕ}
    (hrow : I.RowSumOk M)
    (hcol : I.ColSumOk M)
    (hclose : CloseToBary m I M) :
    I.HallCuts M := by
  -- trivial cuts:
  -- U = ∅, S = ∅: zero
  -- U = univ: follows from column sums
  -- S = univ: follows from row sums and restricted double-counting
  -- nontrivial:
  -- |M(U,S) - B(U,S)| ≤ m * U.card * min(|S|, T-|S|)
  -- ≤ m*d*min(...)
  -- < (m^b/T)*min(...) ≤ slack
```

Now compose rounding + Hall:

```lean
theorem exists_countMatrix_with_residues_of_slack
    {m b d T : ℕ} [NeZero m]
    (hmpos : 0 < m) (hT2 : 2 ≤ T)
    (I : Incidence T X C)
    (hC : Fintype.card C = d)
    (hXmod : (Fintype.card X : ZMod m) = 0)
    (hRowMod : ∀ c : C, (I.colorDegree c : ZMod m) = 0)
    (hRoom : ∀ c σ, (m : ℚ) ≤ I.bary c σ)
    (hSlack : HallSlackBound m b I)
    (hbig : m^b > m * d * T)
    (R : ResidueSpec m T C) :
    ∃ M : CountMatrix I, HasResidues M.val R := by
  -- use ResidueSpec.sum_target_symbols and sum_target_colors
  -- use residue_transport_rounding_close
  -- use hallCuts_of_closeToBary
```

Hoffman realization:

```lean
/-- Active Hall/Hoffman realization.  Hard max-flow/TU statement. -/
axiom exists_symboling_of_countMatrix
    {T : ℕ} {X C : Type*}
    [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    (I : Incidence T X C) (M : CountMatrix I) :
    ∃ Φ : Symboling I, Φ.Realizes M.val
```

Then the main abstract active theorem:

```lean
theorem exists_symboling_of_slack
    {m b d T : ℕ} [NeZero m]
    (hmpos : 0 < m) (hT2 : 2 ≤ T)
    (I : Incidence T X C)
    (hC : Fintype.card C = d)
    (hXmod : (Fintype.card X : ZMod m) = 0)
    (hRowMod : ∀ c : C, (I.colorDegree c : ZMod m) = 0)
    (hRoom : ∀ c σ, (m : ℚ) ≤ I.bary c σ)
    (hSlack : HallSlackBound m b I)
    (hbig : m^b > m * d * T)
    (R : ResidueSpec m T C) :
    ∃ Φ : Symboling I, Φ.HasResidues R := by
  obtain ⟨M, hMres⟩ :=
    exists_countMatrix_with_residues_of_slack
      hmpos hT2 I hC hXmod hRowMod hRoom hSlack hbig R
  obtain ⟨Φ, hreal⟩ := exists_symboling_of_countMatrix I M
  exact ⟨Φ, by intro c σ; simpa [Symboling.HasResidues, hreal c σ] using hMres c σ⟩
```

---

## 5. Base-tail layer

Put this in `BaseTail/Setup.lean`, `BaseTail/Incidence.lean`, `BaseTail/Certificate.lean`.

Basic types:

```lean
namespace BaseTail

abbrev BaseVertex (m b : ℕ) := Fin (b + 1) → ZMod m

abbrev Color {b : ℕ} (k : Fin b → ℕ) :=
  Sigma fun j : Fin b => Fin (k j)

theorem card_baseVertex (m b : ℕ) [NeZero m] :
    Fintype.card (BaseVertex m b) = m^(b + 1) := by
  -- Fintype.card_fun, ZMod.card

theorem card_color {b : ℕ} (k : Fin b → ℕ) :
    Fintype.card (Color k) = ∑ j : Fin b, k j := by
  -- Fintype.card_sigma

noncomputable def colorEquivFin
    {b d : ℕ} {k : Fin b → ℕ}
    (hk_sum : (∑ j : Fin b, k j) = d) :
    Color k ≃ Fin d := by
  -- Fintype.equivFinOfCardEq using card_color
```

Positive unit sums.  If the repo already has this notion, define an adapter instead of duplicating it.

```lean
structure PositiveUnitSum (m k : ℕ) where
  a : Fin k → ℕ
  pos : ∀ i, 0 < a i
  unit : ∀ i, IsUnit ((a i : ZMod m))
  sum_eq : (∑ i : Fin k, a i) = m
```

Active incidence from the base-tail construction:

```lean
noncomputable def activeIncidence
    {m b T : ℕ} [NeZero m]
    (Hb : Shared.CayleyHamiltonDecomposition b m)
    (k : Fin b → ℕ)
    (hkT : (∑ j : Fin b, (k j - 1)) = T) :
    ActiveHall.Incidence T (BaseVertex m b) (Color k) := by
  -- build from cylinder decompositions of Hb and the k_j split
```

Key properties needed by `ActiveHall.exists_symboling_of_slack`:

```lean
theorem activeIncidence_cardX
    {m b T : ℕ} [NeZero m]
    (Hb : Shared.CayleyHamiltonDecomposition b m)
    (k : Fin b → ℕ) (hkT) :
    Fintype.card (BaseVertex m b) = m^(b + 1) :=
  card_baseVertex m b

theorem activeIncidence_X_mod
    {m b T : ℕ} [NeZero m] (hmpos : 0 < m)
    (Hb : Shared.CayleyHamiltonDecomposition b m)
    (k : Fin b → ℕ) (hkT) :
    (Fintype.card (BaseVertex m b) : ZMod m) = 0 := by
  -- card is m^(b+1), divisible by m since b+1 > 0

theorem activeIncidence_row_mod
    {m b T : ℕ} [NeZero m]
    (Hb : Shared.CayleyHamiltonDecomposition b m)
    (k : Fin b → ℕ) (hkT)
    (c : Color k) :
    ((activeIncidence Hb k hkT).colorDegree c : ZMod m) = 0 := by
  -- prove color active counts are multiples of m
```

Slack:

```lean
theorem activeIncidence_mixedExpansion
    {m b T : ℕ} [NeZero m]
    (Hb : Shared.CayleyHamiltonDecomposition b m)
    (k : Fin b → ℕ) (hkT)
    (hTb : T > b) :
    ActiveHall.MixedExpansion m b (activeIncidence Hb k hkT) := by
  -- use root-flat / skew-product / single-cycle lemmas

theorem activeIncidence_hallSlack
    {m b T : ℕ} [NeZero m]
    (Hb : Shared.CayleyHamiltonDecomposition b m)
    (k : Fin b → ℕ) (hkT)
    (hTpos : 0 < T) (hTb : T > b) :
    ActiveHall.HallSlackBound m b (activeIncidence Hb k hkT) :=
  ActiveHall.hallSlackBound_of_mixedExpansion
    (activeIncidence Hb k hkT) hTpos
    (activeIncidence_mixedExpansion Hb k hkT hTb)
```

You also need a “room” lemma for rounding:

```lean
theorem activeIncidence_bary_room
    {m b d T : ℕ} [NeZero m]
    (hmpos : 0 < m)
    (Hb : Shared.CayleyHamiltonDecomposition b m)
    (k : Fin b → ℕ) (hkT)
    (hC : Fintype.card (Color k) = d)
    (hbig : m^b > m * d * T) :
    ∀ c σ, (m : ℚ) ≤
      (activeIncidence Hb k hkT).bary c σ := by
  -- This is a necessary lower-bound lemma.
  -- It must follow from the specific base-tail incidence.
```

This `bary_room` lemma is important.  Without some lower bound on every row, residue rounding can fail by nonnegativity.

Certificate consumed by torus construction:

```lean
structure ActiveCertificate
    {m b d T : ℕ} [NeZero m]
    (Hb : Shared.CayleyHamiltonDecomposition b m)
    (k : Fin b → ℕ) (hkT)
    (R : ActiveHall.ResidueSpec m T (Color k)) where
  Φ : ActiveHall.Symboling (activeIncidence Hb k hkT)
  residues : Φ.HasResidues R
```

Producer:

```lean
theorem activeCertificate_of_hallSlack
    {m b d T : ℕ} [NeZero m]
    (hmpos : 0 < m) (hm_odd : Odd m)
    (hd_odd : Odd d) (hd3 : 3 ≤ d)
    (Hb : Shared.CayleyHamiltonDecomposition b m)
    (k : Fin b → ℕ) (hkT)
    (hk_sum : (∑ j : Fin b, k j) = d)
    (hT2 : 2 ≤ T)
    (hTb : T > b)
    (hbig : m^b > m * d * T) :
    ∃ R : ActiveHall.ResidueSpec m T (Color k),
    ∃ cert : ActiveCertificate Hb k hkT R, True := by
  let I := activeIncidence Hb k hkT
  have hC : Fintype.card (Color k) = d := by
    simpa [card_color] using hk_sum
  let R := ActiveHall.oddResidueSpec hm_odd hd_odd hd3 (Color k) hC
  have hXmod := activeIncidence_X_mod hmpos Hb k hkT
  have hRowMod := activeIncidence_row_mod Hb k hkT
  have hSlack := activeIncidence_hallSlack Hb k hkT (by omega) hTb
  have hRoom := activeIncidence_bary_room hmpos Hb k hkT hC hbig
  obtain ⟨Φ, hΦ⟩ :=
    ActiveHall.exists_symboling_of_slack
      hmpos hT2 I hC hXmod hRowMod hRoom hSlack hbig R
  exact ⟨R, ⟨Φ, hΦ⟩, trivial⟩
```

Consumer into `CayleyHamiltonDecomposition`:

```lean
theorem chd_of_activeCertificate
    {m b d T : ℕ} [NeZero m]
    (hmpos : 0 < m)
    (hd_eq : d = b + T)
    (Hb : Shared.CayleyHamiltonDecomposition b m)
    (k : Fin b → ℕ)
    (hk_sum : (∑ j : Fin b, k j) = d)
    (hk_units : ∀ j : Fin b, PositiveUnitSum m (k j))
    (hkT : (∑ j : Fin b, (k j - 1)) = T)
    (R : ActiveHall.ResidueSpec m T (Color k))
    (cert : ActiveCertificate Hb k hkT R) :
    Shared.CayleyHamiltonDecomposition d m := by
  -- Use existing product/composite lift infrastructure,
  -- root-flat/skew-product/single-cycle lemmas,
  -- and prefix-count unit lemmas.
```

Finally:

```lean
theorem hallSlackBranch_add
    {m b d T : ℕ} [NeZero m]
    (hm3 : 3 ≤ m) (hm_odd : Odd m)
    (hd_odd : Odd d)
    (hbpos : 0 < b)
    (hd_eq : d = b + T)
    (Hb : Shared.CayleyHamiltonDecomposition b m)
    (k : Fin b → ℕ)
    (hk_sum : (∑ j : Fin b, k j) = d)
    (hk_units : ∀ j : Fin b, PositiveUnitSum m (k j))
    (hTb : T > b)
    (hbig : m^b > m * d * T) :
    Shared.CayleyHamiltonDecomposition d m := by
  have hmpos : 0 < m := by omega
  have hTpos : 0 < T := by omega
  have hT2 : 2 ≤ T := by omega
  have hd3 : 3 ≤ d := by omega
  have hkT : (∑ j : Fin b, (k j - 1)) = T := by
    -- from hk_units get ∀ j, 0 < k j, then omega/finset arithmetic
    sorry
  obtain ⟨R, cert, -⟩ :=
    activeCertificate_of_hallSlack
      hmpos hm_odd hd_odd hd3 Hb k hkT hk_sum hT2 hTb hbig
  exact chd_of_activeCertificate
    hmpos hd_eq Hb k hk_sum hk_units hkT R cert
```

---

## 6. What is likely in mathlib vs custom/axiom?

### Likely already in mathlib

- `Finset` sums/cards, `Fintype.card_sigma`, `Fintype.card_fun`.
- `ZMod`, cardinality of `ZMod m`, units in `ZMod m`.
- `Odd`, `Nat.Coprime`, arithmetic via `omega`, `nlinarith`.
- Equivalences from cardinal equality: `Fintype.equivFinOfCardEq`.
- Basic finite double-counting can be proved directly with `Finset.sum_card`.

### Should be proved directly in the repo

- `Incidence.sum_colorDegree`, `sum_colorDegree_on`.
- Symboling row/column count lemmas.
- Residue target sum lemmas.
- Odd residue pattern `1,1,-2` plus pairs `1,-1`.
- Barycenter Hall membership.
- `MixedExpansion → HallSlackBound`.
- `CloseToBary + HallSlackBound + hbig → HallCuts`.
- Card lemmas for `BaseVertex` and `Color`.
- Row divisibility and `Xmod` for the concrete base-tail incidence.
- The certificate consumer `chd_of_activeCertificate`.

### Temporarily axiomatize, or isolate very carefully

1. **Hoffman/TU realization**
   ```lean
   axiom ActiveHall.exists_symboling_of_countMatrix ...
   ```
   This is the active matrix-to-symboling theorem.  Mathlib may have Hall matching, but this is capacitated multi-symbol Hoffman, not a trivial import.

2. **Controlled modular transportation rounding**
   ```lean
   axiom ActiveHall.residue_transport_rounding_close ...
   ```
   This is another finite-flow/TU theorem.  It is independent of tori and should stay isolated.

3. **Concrete root-flat mixed expansion**, only if existing root-flat lemmas do not immediately give it:
   ```lean
   theorem BaseTail.activeIncidence_mixedExpansion ...
   ```
   Prefer proving this from existing root-flat/skew-product/single-cycle lemmas.

---

## 7. Certificate alternative if Hoffman/TU is too expensive

The torus construction should consume only:

```lean
structure ActiveCertificate
    (Hb : Shared.CayleyHamiltonDecomposition b m)
    (k : Fin b → ℕ) (hkT)
    (R : ActiveHall.ResidueSpec m T (Color k)) where
  Φ : ActiveHall.Symboling (activeIncidence Hb k hkT)
  residues : Φ.HasResidues R
```

Then the global torus theorem can be split:

```lean
theorem chd_of_activeCertificate : ... → Shared.CayleyHamiltonDecomposition d m
```

and the hard active existence theorem can be a separately audited axiom:

```lean
axiom exists_activeCertificate_of_hallSlack
    -- manuscript hypotheses
    :
    ∃ R, ∃ cert : ActiveCertificate Hb k hkT R, True
```

This is much better than axiomatizing the final Hamilton decomposition theorem.  It localizes the unformalized polyhedral content to exactly the active symboling existence statement.

For concrete finite experiments, you can add a boolean checker:

```lean
structure RawSymboling (I : ActiveHall.Incidence T X C) where
  sym : ∀ x : X, {c : C // c ∈ I.active x} → Fin T

def RawSymboling.ValidBool ... : Bool := ...

theorem certificate_of_validBool_eq_true
    (raw : RawSymboling I)
    (h : raw.ValidBool = true) :
    ActiveHall.Symboling I := ...
```

This is useful for testing but not for the parametric theorem.

---

## 8. Hidden assumptions / formalization blockers

These must be resolved explicitly.

1. **Nontrivial Hall cuts.**
   The slack lower bound is false for `U = univ` and `0 < |S| < T`.  Define nontrivial as:
   ```lean
   U.Nonempty ∧ U.card < Fintype.card C ∧ S.Nonempty ∧ S.card < T
   ```

2. **Need `T ≥ 2`.**
   Symbols `0` and `Delta` must be distinct.  From `hbpos : 0 < b` and `T > b`, Lean can prove `2 ≤ T`.

3. **Residue compatibility requires row divisibility.**
   Since row target residues sum to `0`, every active row count must satisfy:
   ```lean
   ∀ c, (I.colorDegree c : ZMod m) = 0
   ```
   This is not optional.

4. **Column compatibility requires `|X| ≡ 0 mod m`.**
   For `X = (ZMod m)^(b+1)` this is true, but must be proved.

5. **Nonnegativity/rounding room.**
   The controlled rounding theorem needs enough room in every cell, e.g.
   ```lean
   ∀ c σ, (m : ℚ) ≤ I.bary c σ
   ```
   Otherwise unit residue requirements can force positive entries in a row that is too small.  The manuscript’s numerical hypothesis must imply this through the concrete base-tail incidence; formalize it as `activeIncidence_bary_room`.

6. **Clarify “positive units.”**
   If downstream prefix-count lemmas need an actual natural sum equal to `m`, use the stronger structure:
   ```lean
   PositiveUnitSum m k
   ```
   not merely `∑ = 0` in `ZMod m`.

7. **No multiple incidence per `(x,c)`.**
   The Hall model assumes `Γ ⊆ X × C`, not a multiset.  Prove that each color uses at most one active copy at a base vertex.

8. **Color indexing.**
   Use `Color k = Σ j, Fin (k j)` and prove/cardinally identify it with `Fin d`.  If `CayleyHamiltonDecomposition` is hardcoded to `Fin d`, add a relabeling/reindexing lemma.

9. **Constants in rounding.**
   The proof `close → Hall` uses a cellwise error bound `≤ m`.  If the eventual rounding theorem only gives `≤ m + 1`, the hypothesis `m^b > m*d*T` may be insufficient.  Fix the exact bound before proving the arithmetic.

---

## 9. Recommended implementation order

1. `ActiveHall/Basic.lean`: incidence, matrices, symbolings, double-counting.
2. `ActiveHall/Residues.lean`: residue specs, odd residue pattern.
3. `ActiveHall/Slack.lean`: barycenter formulas, mixed expansion implies slack.
4. `ActiveHall/Rounding.lean`: state modular rounding axiom; prove close-to-bary implies Hall.
5. `ActiveHall/Hoffman.lean`: state Hoffman realization axiom.
6. `BaseTail/Setup.lean`: `BaseVertex`, `Color`, cardinal lemmas, `PositiveUnitSum`.
7. `BaseTail/Incidence.lean`: construct active incidence; prove `active_card`, row mod, `Xmod`, mixed expansion, bary room.
8. `BaseTail/Certificate.lean`: define active certificate; prove `chd_of_activeCertificate`.
9. `BaseTail/HallSlackBranch.lean`: combine everything into `hallSlackBranch_add` and `hallSlackBranch_sub`.

This keeps the hard polyhedral content isolated, while allowing the torus construction and certificate consumer to be implemented and tested immediately.