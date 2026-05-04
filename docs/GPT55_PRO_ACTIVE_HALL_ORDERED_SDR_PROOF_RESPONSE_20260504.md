# GPT-5.5 Pro Active Hall Ordered-SDR Proof Response

Date: 2026-05-04.

Response id: `resp_050d642997a6ebc00069f8dceccb388192ae6b3842da834279`.

Status: `completed`.

---

Below is the Lean-facing route I would implement.  I do **not** see a direct current-mathlib theorem strong enough beyond ordinary Hall, so the cleanest close is to add one finite external theorem in copied-edge/edge-colouring form, then derive the exact `ActiveHall` target by short adapters.

The point is to avoid encoding Hoffman's theorem directly in terms of `Symboling`; instead add a reusable theorem about colouring the copied demand edges of a bipartite multigraph.

---

## 1. Add this external finite theorem

Put this near the abstract goals in `RoundComposite/ActiveHall.lean`, e.g. before `HoffmanOrderedSDRGoal`.

```lean
namespace FiniteHoffman

open scoped BigOperators

def edgeLeftDegree {T : Nat} {C E : Type*}
    [Fintype E] [DecidableEq C]
    (left : E → C) (c : C) : Nat :=
  ((Finset.univ : Finset E).filter (fun e => left e = c)).card

def edgeRightDegree {T : Nat} {E : Type*}
    [Fintype E]
    (right : E → Fin T) (σ : Fin T) : Nat :=
  ((Finset.univ : Finset E).filter (fun e => right e = σ)).card

def edgeRectCount {T : Nat} {C E : Type*}
    [Fintype E] [DecidableEq C]
    (left : E → C) (right : E → Fin T)
    (U : Finset C) (S : Finset (Fin T)) : Nat :=
  ((Finset.univ : Finset E).filter
    (fun e => left e ∈ U ∧ right e ∈ S)).card

def edgePairCount {T : Nat} {C E : Type*}
    [Fintype E] [DecidableEq C]
    (left : E → C) (right : E → Fin T)
    (c : C) (σ : Fin T) : Nat :=
  ((Finset.univ : Finset E).filter
    (fun e => left e = c ∧ right e = σ)).card

def activeDegree {X C : Type*}
    [Fintype X] [DecidableEq C]
    (active : X → Finset C) (c : C) : Nat :=
  ((Finset.univ : Finset X).filter (fun x => c ∈ active x)).card

/--
External finite Hoffman/de Werra edge-colouring theorem.

`E` is the copied edge set of a bipartite multigraph with left side `C` and
right side `Fin T`.  The colours are `X`.  Colour `x` may be used on an edge
with left endpoint `c` iff `c ∈ active x`.  The conclusion says that every
right vertex `σ` sees every colour `x` exactly once, and every allowed pair
`(x,c)` occurs exactly once.

The rectangle condition is the Hoffman cut condition.
-/
def ExactEdgeColoringGoal : Prop :=
  ∀ {T : Nat} {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Fintype C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E],
    ∀ (left : E → C) (right : E → Fin T) (active : X → Finset C),
      (∀ x : X, (active x).card = T) →
      (∀ c : C,
        edgeLeftDegree left c = activeDegree active c) →
      (∀ σ : Fin T,
        edgeRightDegree right σ = Fintype.card X) →
      (∀ U : Finset C, ∀ S : Finset (Fin T),
        edgeRectCount left right U S
          ≤ ∑ x : X, min ((active x ∩ U).card) S.card) →
      ∃ κ : E → X,
        (∀ e : E, left e ∈ active (κ e)) ∧
        (∀ x : X, ∀ σ : Fin T,
          ∃! e : E, κ e = x ∧ right e = σ) ∧
        (∀ x : X, ∀ c : C, c ∈ active x →
          ∃! e : E, κ e = x ∧ left e = c)

end FiniteHoffman
```

This is the smallest external theorem I would add.  It is the prescribed one-sided bipartite edge-colouring theorem, but stated directly on copied finite edges, not on `Incidence`, `CountMatrix`, or `Symboling`.

---

## 2. Copied demand-token type and counting lemmas

For `HoffmanOrderedSDRGoal`, instantiate the external theorem with copied demand edges

```lean
abbrev DemandToken {T : Nat} {C : Type uC}
    (m : C → Fin T → Nat) : Type uC :=
  Sigma fun c : C => Sigma fun σ : Fin T => Fin (m c σ)

namespace DemandToken

def color {T : Nat} {C : Type uC} {m : C → Fin T → Nat}
    (q : DemandToken m) : C :=
  q.1

def sym {T : Nat} {C : Type uC} {m : C → Fin T → Nat}
    (q : DemandToken m) : Fin T :=
  q.2.1
```

Add these counting lemmas.  Their proofs are routine by `Finset.card_filter`,
`Fintype.sum_sigma`, and `simp`.

```lean
theorem edgeLeftDegree_color
    {T : Nat} {C : Type uC} [Fintype C] [DecidableEq C]
    (m : C → Fin T → Nat) (c : C) :
    FiniteHoffman.edgeLeftDegree
        (fun q : DemandToken m => DemandToken.color q) c
      = ∑ σ : Fin T, m c σ := by
  classical
  -- `rw [FiniteHoffman.edgeLeftDegree, Finset.card_filter]`
  -- then two `Fintype.sum_sigma` and `simp`.
  sorry

theorem edgeRightDegree_sym
    {T : Nat} {C : Type uC} [Fintype C] [DecidableEq C]
    (m : C → Fin T → Nat) (σ : Fin T) :
    FiniteHoffman.edgeRightDegree
        (fun q : DemandToken m => DemandToken.sym q) σ
      = ∑ c : C, m c σ := by
  classical
  sorry

theorem edgeRectCount_color_sym
    {T : Nat} {C : Type uC} [Fintype C] [DecidableEq C]
    (m : C → Fin T → Nat)
    (U : Finset C) (S : Finset (Fin T)) :
    FiniteHoffman.edgeRectCount
        (fun q : DemandToken m => DemandToken.color q)
        (fun q : DemandToken m => DemandToken.sym q) U S
      = ∑ c ∈ U, ∑ σ ∈ S, m c σ := by
  classical
  sorry

theorem edgePairCount_color_sym
    {T : Nat} {C : Type uC} [Fintype C] [DecidableEq C]
    (m : C → Fin T → Nat) (c : C) (σ : Fin T) :
    FiniteHoffman.edgePairCount
        (fun q : DemandToken m => DemandToken.color q)
        (fun q : DemandToken m => DemandToken.sym q) c σ
      = m c σ := by
  classical
  sorry

end DemandToken
```

These four lemmas are the only copied-token arithmetic needed.

---

## 3. Convert an exact edge-colouring to local equivalences

From the external theorem’s colouring

```lean
κ : E → X
```

build, for every `x`, an equivalence

```lean
Fin T ≃ {c : C // c ∈ active x}
```

using the two uniqueness clauses.

Recommended helpers:

```lean
namespace FiniteHoffman

noncomputable def rightEdge
    {T : Nat} {X C E : Type*}
    (left : E → C) (right : E → Fin T) (active : X → Finset C)
    (κ : E → X)
    (hRight : ∀ x : X, ∀ σ : Fin T,
      ∃! e : E, κ e = x ∧ right e = σ)
    (x : X) (σ : Fin T) : E :=
  Classical.choose ((hRight x σ).exists)

theorem rightEdge_spec
    {T : Nat} {X C E : Type*}
    (left : E → C) (right : E → Fin T) (active : X → Finset C)
    (κ : E → X)
    (hRight : ∀ x : X, ∀ σ : Fin T,
      ∃! e : E, κ e = x ∧ right e = σ)
    (x : X) (σ : Fin T) :
    κ (rightEdge left right active κ hRight x σ) = x ∧
      right (rightEdge left right active κ hRight x σ) = σ := by
  classical
  exact Classical.choose_spec ((hRight x σ).exists)
```

Similarly define `leftEdge` from the left uniqueness clause.

Then define:

```lean
noncomputable def localEquivOfExactColoring
    {T : Nat} {X C E : Type*} [DecidableEq C]
    (left : E → C) (right : E → Fin T) (active : X → Finset C)
    (κ : E → X)
    (hAvail : ∀ e : E, left e ∈ active (κ e))
    (hRight : ∀ x : X, ∀ σ : Fin T,
      ∃! e : E, κ e = x ∧ right e = σ)
    (hLeft : ∀ x : X, ∀ c : C, c ∈ active x →
      ∃! e : E, κ e = x ∧ left e = c)
    (x : X) :
    Fin T ≃ {c : C // c ∈ active x} := by
  classical
  refine
  { toFun := ?toFun
    invFun := ?invFun
    left_inv := ?left_inv
    right_inv := ?right_inv }
  · intro σ
    let e := rightEdge left right active κ hRight x σ
    refine ⟨left e, ?_⟩
    have he := rightEdge_spec left right active κ hRight x σ
    simpa [he.1] using hAvail e
  · intro c
    let e := Classical.choose ((hLeft x c.1 c.2).exists)
    exact right e
  ·
    -- Use left uniqueness: the edge chosen by `invFun (toFun σ)`
    -- has the same colour `x` and same left endpoint as `rightEdge x σ`;
    -- hence it is the same edge, so its right endpoint is `σ`.
    intro σ
    -- implement by extracting `ExistsUnique.unique`.
    sorry
  ·
    -- Use right uniqueness analogously.
    intro c
    apply Subtype.ext
    -- implement by uniqueness.
    sorry
```

Finally add the counting lemma:

```lean
theorem choiceDegree_localEquivOfExactColoring
    {T : Nat} {X C E : Type*}
    [Fintype X] [Fintype E]
    [DecidableEq X] [DecidableEq C]
    (left : E → C) (right : E → Fin T) (active : X → Finset C)
    (κ : E → X)
    (hAvail : ∀ e : E, left e ∈ active (κ e))
    (hRight : ∀ x : X, ∀ σ : Fin T,
      ∃! e : E, κ e = x ∧ right e = σ)
    (hLeft : ∀ x : X, ∀ c : C, c ∈ active x →
      ∃! e : E, κ e = x ∧ left e = c)
    (c : C) (σ : Fin T) :
    Incidence.choiceDegree
        (fun x : X =>
          ((localEquivOfExactColoring
              left right active κ hAvail hRight hLeft x) σ).1) c
      =
    edgePairCount left right c σ := by
  classical
  -- Use `Finset.card_bij`.
  -- Forward map:
  --   x ↦ rightEdge left right active κ hRight x σ.
  -- The equality of chosen colour with `c` gives `left e = c`;
  -- `rightEdge_spec` gives `right e = σ`.
  -- Inverse map:
  --   e ↦ κ e.
  -- Right uniqueness proves the maps are inverse.
  sorry

end FiniteHoffman
```

This lemma is important: it avoids painful direct reasoning about `choiceDegree`.

---

## 4. Main adapter: external edge theorem implies `HoffmanOrderedSDRGoal`

This is the theorem that actually closes the preferred target.

```lean
theorem hoffmanOrderedSDRGoal_of_exactEdgeColoring
    (hEdge : FiniteHoffman.ExactEdgeColoringGoal.{uX, uC}) :
    HoffmanOrderedSDRGoal.{uX, uC} := by
  classical
  intro T X C _instX _instC _decX _decC I m hrow hcol hcut

  let E : Type uC := DemandToken m
  let left : E → C := fun q => DemandToken.color q
  let right : E → Fin T := fun q => DemandToken.sym q

  have hAct : ∀ x : X, (I.active x).card = T := by
    intro x
    exact I.active_card x

  have hLeft :
      ∀ c : C,
        FiniteHoffman.edgeLeftDegree left c =
          FiniteHoffman.activeDegree I.active c := by
    intro c
    rw [DemandToken.edgeLeftDegree_color]
    simpa [FiniteHoffman.activeDegree, Incidence.colorDegree] using hrow c

  have hRight :
      ∀ σ : Fin T,
        FiniteHoffman.edgeRightDegree right σ = Fintype.card X := by
    intro σ
    rw [DemandToken.edgeRightDegree_sym]
    exact hcol σ

  have hRect :
      ∀ U : Finset C, ∀ S : Finset (Fin T),
        FiniteHoffman.edgeRectCount left right U S
          ≤ ∑ x : X, min ((I.active x ∩ U).card) S.card := by
    intro U S
    rw [DemandToken.edgeRectCount_color_sym]
    simpa [Incidence.cutCap] using hcut U S

  rcases hEdge left right I.active hAct hLeft hRight hRect with
    ⟨κ, hAvail, hκRight, hκLeft⟩

  let e : ∀ x : X, Fin T ≃ {c : C // c ∈ I.active x} :=
    fun x =>
      FiniteHoffman.localEquivOfExactColoring
        left right I.active κ hAvail hκRight hκLeft x

  refine ⟨e, ?_⟩
  intro c σ
  calc
    Incidence.choiceDegree (fun x : X => ((e x) σ).1) c
        =
      FiniteHoffman.edgePairCount left right c σ := by
        exact FiniteHoffman.choiceDegree_localEquivOfExactColoring
          left right I.active κ hAvail hκRight hκLeft c σ
    _ = m c σ := by
        exact DemandToken.edgePairCount_color_sym m c σ
```

After this, the existing file already gives:

```lean
theorem hallRealizationGoal_of_exactEdgeColoring
    (hEdge : FiniteHoffman.ExactEdgeColoringGoal.{uX, uC}) :
    HallRealizationGoal.{uX, uC} :=
  hallRealizationGoal_of_hoffmanOrderedSDR
    (hoffmanOrderedSDRGoal_of_exactEdgeColoring hEdge)

theorem eraseLastHallCutsTokenLinearChoiceGoal_of_exactEdgeColoring
    (hEdge : FiniteHoffman.ExactEdgeColoringGoal.{uX, uC}) :
    EraseLastHallCutsTokenLinearChoiceGoal.{uX, uC} :=
  eraseLastHallCutsTokenLinearChoiceGoal_of_hallRealization
    (hallRealizationGoal_of_exactEdgeColoring hEdge)
```

So the exact requested target closes from the one external theorem.

---

## 5. How the current `cutMass`, `cutSlack`, `lowCutSet`, and `tokenLoadOn` enter

The adapter above proves `HoffmanOrderedSDRGoal`.  Then the already-existing theorem

```lean
eraseLastHallCutsTokenLinearChoiceGoal_of_hallRealization
```

does the erase-last work.

Concretely, for `I : Incidence (T + 1) X C`, `M : CountMatrix I`, and `hHall : M.HallCuts`:

1. `hallRealizationGoal_of_exactEdgeColoring hEdge` gives a full symboling

   ```lean
   Φ : Symboling I
   hReal : Φ.Realizes M.val
   ```

2. Take the last-symbol choice

   ```lean
   choice x := Φ.color x (Fin.last T)
   ```

3. Use the existing copied-token lemma

   ```lean
   Incidence.exists_choiceDegree_bijective_token_matching
   ```

   to get

   ```lean
   f : (Sigma fun c : C => Fin (M.val c (Fin.last T))) ≃ X
   ```

   with token colour equal to `choice (f q)`.

4. For every lower cut `U,S`, the existing symboling lemma gives

   ```lean
   M.cutMass U (S.image Fin.castSucc)
     + Incidence.choiceLowHitCount I choice U S
       ≤ I.cutCap U (S.image Fin.castSucc)
   ```

5. Since `hHall` gives

   ```lean
   M.cutMass U (S.image Fin.castSucc)
     ≤ I.cutCap U (S.image Fin.castSucc)
   ```

   the existing arithmetic lemma

   ```lean
   CountMatrix.cutMass_add_le_iff_le_cutSlack
   ```

   yields

   ```lean
   Incidence.choiceLowHitCount I choice U S
     ≤ M.cutSlack U (S.image Fin.castSucc)
   ```

6. Finally the current identification lemmas

   ```lean
   Incidence.choiceLowHitCount_eq_choiceHitCountOn_lowCutSet
   Incidence.tokenLoadOn_eq_choiceHitCountOn
   ```

   rewrite this as the exact token-linear inequality

   ```lean
   Incidence.tokenLoadOn f (Incidence.lowCutSet I U S) U
     ≤ M.cutSlack U (S.image Fin.castSucc)
   ```

Thus `cutMass` and `cutCap` are used in the Hoffman realization adapter, while `cutSlack`, `lowCutSet`, and `tokenLoadOn` are used by the existing erase-last bridge.

---

## 6. Proof outline for the external theorem

The theorem `FiniteHoffman.ExactEdgeColoringGoal` is the standard finite Hoffman/de Werra prescribed edge-colouring theorem.

A Lean proof can be organized by induction on `T`:

* `T = 0`: `active x` has card `0`, right side is empty, and the degree hypotheses force `E` empty.

* `T + 1`: colour the last right fibre first.  The last fibre is

  ```lean
  {e : E // right e = Fin.last T}
  ```

  and `edgeRightDegree right (Fin.last T) = Fintype.card X` gives the correct number of copied last edges.  The one-fibre Hall condition is the rectangle cut with `S = {Fin.last T}`:

  ```lean
  edgeRectCount left right U {Fin.last T}
    ≤ ∑ x, min ((active x ∩ U).card) 1
  ```

  which is exactly the Hall neighbourhood bound for matching last-fibre edges to colours `x` with `left e ∈ active x`.

  The nontrivial part is choosing this matching so that all residual rectangle cuts remain true.  This is Perfect/Hoffman’s last-fibre lemma: among all Hall matchings of the last fibre, choose one minimizing the finite vector of residual cut violations; an alternating-path exchange reduces any positive violation, while absence of an exchange produces a violated original rectangle cut.  This is the classical de Werra proof.

  After this last-fibre colouring:
  * remove the last right fibre;
  * replace each `active x` by `active x \ {chosen left colour at x}`;
  * reindex the remaining right side by `Fin T`;
  * the residual rectangle inequalities are exactly the old inequalities minus the local drop

    ```lean
    if chosenColor x ∈ U ∧ (active x ∩ U).card ≤ S.card then 1 else 0
    ```

    which is the same low-cut term already represented in `ActiveHall` by
    `lowCutSet` and `choiceLowHitCount`.

  Then apply the induction hypothesis and extend by the last fibre.

This proof outline is exactly aligned with the erase-last infrastructure already in `ActiveHall.lean`; the difference is that the external theorem packages the hard Perfect/Hoffman last-fibre selection once, in copied-edge form.
