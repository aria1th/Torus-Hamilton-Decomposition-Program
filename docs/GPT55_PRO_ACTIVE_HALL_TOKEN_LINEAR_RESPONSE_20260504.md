# GPT-5.5 Pro Active Hall Token-Linear Response

Date: 2026-05-04.

Response id: `resp_0e21b390daf9f8440069f8144e4968819583e275bf3d78e6e8`.

## Short answer

The stated token-linear theorem is **true**. It is not a consequence of the already-proved one-column Hall matching alone. The exact finite theorem you need is the classical **Hoffman ordered-SDR theorem**, equivalently the **one-sided prescribed-degree edge-colouring theorem for bipartite graphs**.

In the current language, this theorem is essentially `HallRealizationGoal`: given finite `T`-subsets `I.active x` and a matrix `M` with the forced row/column sums, the rectangle inequalities

```lean
M.cutMass U S ≤ I.cutCap U S
```

are necessary and sufficient for choosing, for every `x`, a bijection

```lean
Fin T ≃ {c : C // c ∈ I.active x}
```

with prescribed symbol counts `M.val c σ`.

Once this Hoffman theorem is available, your remaining theorem follows immediately through the already-closed bridge

```lean
eraseLastHallCutsTokenLinearChoiceGoal_of_hallRealization
```

so there is no finite counterexample to the target as stated.

---

## 1. Lean-friendly intermediate theorem

A good standalone theorem to formalize is this, avoiding `CountMatrix` in the statement but using the existing `Incidence` vocabulary.

```lean
def HoffmanOrderedSDRGoal : Prop :=
  ∀ {T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence T X C) (m : C → Fin T → Nat),
      (∀ c : C, (∑ σ : Fin T, m c σ) = I.colorDegree c) →
      (∀ σ : Fin T, (∑ c : C, m c σ) = Fintype.card X) →
      (∀ U : Finset C, ∀ S : Finset (Fin T),
        (∑ c ∈ U, ∑ σ ∈ S, m c σ) ≤ I.cutCap U S) →
      ∃ e : (∀ x : X, Fin T ≃ {c : C // c ∈ I.active x}),
        ∀ c σ,
          Incidence.choiceDegree (fun x : X => ((e x) σ).1) c = m c σ
```

Mathematically: given `T`-element sets `A_x ⊆ C`, and target counts `m c σ`, there exist orderings of every `A_x` by symbols `σ : Fin T` realizing the counts iff for every `U ⊆ C` and `S ⊆ Fin T`,

\[
\sum_{c\in U,\ \sigma\in S} m_{c,\sigma}
\le
\sum_x \min(|A_x \cap U|, |S|).
\]

This is Hoffman's theorem on ordered systems of distinct representatives. Equivalently, it is the prescribed-degree one-sided edge-colouring theorem for a bipartite graph with left side `X`, right side `C`, and edge `x -- c` iff `c ∈ I.active x`.

---

## 2. How `M.HallCuts` gives the hypotheses

Given

```lean
I : Incidence T X C
M : CountMatrix I
hHall : M.HallCuts
```

instantiate the theorem with

```lean
m := M.val
```

The row-sum hypothesis is exactly:

```lean
M.row_sum : ∀ c, (∑ σ : Fin T, M.val c σ) = I.colorDegree c
```

The column-sum hypothesis is exactly:

```lean
M.col_sum : ∀ σ, (∑ c : C, M.val c σ) = Fintype.card X
```

The cut hypothesis follows by unfolding `CountMatrix.cutMass`:

```lean
have hcut :
    ∀ U : Finset C, ∀ S : Finset (Fin T),
      (∑ c ∈ U, ∑ σ ∈ S, M.val c σ) ≤ I.cutCap U S := by
  intro U S
  simpa [CountMatrix.cutMass] using hHall U S
```

If your version of Hoffman expands `I.cutCap`, then use:

```lean
simpa [CountMatrix.cutMass, Incidence.cutCap] using hHall U S
```

No torus geometry, residues, or additional conditions are involved.

---

## 3. Deriving `HallRealizationGoal` from Hoffman

The adapter is short.

```lean
theorem hallRealizationGoal_of_hoffmanOrderedSDR
    (hHoffman : HoffmanOrderedSDRGoal.{uX, uC}) :
    HallRealizationGoal.{uX, uC} := by
  classical
  intro T X C _instX _instC _decX _decC I M hHall

  rcases hHoffman I M.val M.row_sum M.col_sum
      (by
        intro U S
        simpa [CountMatrix.cutMass] using hHall U S)
    with ⟨e, he⟩

  let Φ : Symboling I := { equiv := e }

  refine ⟨Φ, ?_⟩
  intro c σ
  rw [Symboling.count_eq_choiceDegree]
  simpa [Φ, Symboling.color] using he c σ
```

So `HoffmanOrderedSDRGoal` implies the existing abstract realization theorem.

Conversely, `HallRealizationGoal` implies `HoffmanOrderedSDRGoal` by building a `CountMatrix` from `m`, using the row/column hypotheses, and applying `HallRealizationGoal`. Thus this is not merely a sufficient lemma; it is essentially equivalent to your current `HallRealizationGoal`.

---

## 4. Deriving the token-linear theorem

Once you have the Hoffman theorem, the target follows through your existing bridge:

```lean
theorem eraseLastHallCutsTokenLinearChoiceGoal_of_hoffmanOrderedSDR
    (hHoffman : HoffmanOrderedSDRGoal.{uX, uC}) :
    EraseLastHallCutsTokenLinearChoiceGoal.{uX, uC} :=
  eraseLastHallCutsTokenLinearChoiceGoal_of_hallRealization
    (hallRealizationGoal_of_hoffmanOrderedSDR hHoffman)
```

Internally, the already-closed bridge does the following.

Given a full symboling

```lean
Φ : Symboling I
hReal : Φ.Realizes M.val
```

take the last-symbol choice

```lean
choice x := Φ.color x (Fin.last T)
```

Then:

1. `choice x ∈ I.active x` by `Φ.color_mem_active`.
2. The last-column degrees satisfy

   ```lean
   Incidence.choiceDegree choice c = M.val c (Fin.last T)
   ```

   by `Φ.count_eq_choiceDegree` and `hReal`.

3. Use

   ```lean
   Incidence.exists_choiceDegree_bijective_token_matching
   ```

   to obtain the token bijection

   ```lean
   f : (Sigma fun c => Fin (M.val c (Fin.last T))) ≃ X
   ```

   inducing the same `choice`.

4. The crucial slack estimate comes from the existing local lemma

   ```lean
   Symboling.cutMass_image_castSucc_add_choiceLowHitCount_le_cutCap_of_realizes
   ```

   which gives

   ```lean
   M.cutMass U (S.image Fin.castSucc)
     + Incidence.choiceLowHitCount I choice U S
   ≤ I.cutCap U (S.image Fin.castSucc)
   ```

5. Combining this with `hHall U (S.image Fin.castSucc)` and

   ```lean
   CountMatrix.cutMass_add_le_iff_le_cutSlack
   ```

   gives

   ```lean
   Incidence.choiceLowHitCount I choice U S
     ≤ M.cutSlack U (S.image Fin.castSucc)
   ```

6. Finally,

   ```lean
   Incidence.tokenLoadOn_eq_choiceHitCountOn
   Incidence.choiceLowHitCount_eq_choiceHitCountOn_lowCutSet
   ```

   identify the token load with the low-hit count.

This is exactly the proof already encoded in

```lean
eraseLastHallCutsTokenLinearChoiceGoal_of_hallRealization
```

---

## 5. Why plain Hall matching is insufficient

The theorem needed is stronger than independent Hall matchings for each column.

Example: take

```lean
T = 2
X = Fin 2
C = Fin 2
I.active x = Finset.univ
M.val c σ = 1
```

Then every column separately has a Hall matching. But choosing the same matching in both columns gives a valid `ColumnFilling`:

```text
x = 0 gets color 0 in both symbols
x = 1 gets color 1 in both symbols
```

The prescribed column counts are correct, and all colors are active, but this is not a `Symboling`, because at each vertex the two chosen colors are not distinct. A genuine symboling exists by swapping one column, but plain Hall gives no mechanism forcing that coordination.

So the correct strengthening is not “more Hall per column”; it is Hoffman's ordered-SDR / prescribed one-sided bipartite edge-colouring theorem.

---

## 6. Counterexample risk

There is no counterexample to the stated token-linear theorem in finite combinatorics, assuming the standard Hoffman theorem. The target is equivalent, via your existing Lean bridges, to the finite Hoffman realization theorem.

A counterexample would disprove Hoffman's ordered-SDR theorem. The small brute-force search is therefore consistent with the known theorem, not merely suggestive.
