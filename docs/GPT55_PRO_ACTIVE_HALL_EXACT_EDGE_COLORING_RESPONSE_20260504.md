# GPT-5.5 Pro Active-Hall Exact Edge-Coloring Response

Date: 2026-05-04.

Response id: `resp_0cd087a6b2f8d1cf0069f8e8faaf4881a0beb65e653ae30d4c`.

Status: `completed`.

---

The cleanest Lean-facing route is to import/use the finite Hoffman–de Werra compatible bipartite edge-colouring theorem, then adapt its edge-colouring map `κ : E → X` to your required local equivalences.  The adapter is short and preserves the exact copied-edge pair counts.

Below, `CompatibleDeWerraGoal` is the one external theorem I would add/prove.

```lean
namespace RoundComposite.ActiveHall.FiniteHoffman

open scoped BigOperators

/-- Finite Hoffman/de Werra compatible edge-colouring theorem.

`A k` is the set of left vertices where colour `k` is allowed,
`B k` is the set of right vertices where colour `k` is allowed.
The conclusion says each listed colour is used exactly once at each listed
vertex. -/
def CompatibleDeWerraGoal : Prop :=
  ∀ {L R K E : Type*}
    [Fintype L] [Fintype R] [Fintype K] [Fintype E]
    [DecidableEq L] [DecidableEq R] [DecidableEq K] [DecidableEq E],
    ∀ (left : E → L) (right : E → R)
      (A : K → Finset L) (B : K → Finset R),
      (∀ k : K, (A k).card = (B k).card) →
      (∀ l : L,
        (Finset.univ.filter (fun e : E => left e = l)).card =
          (Finset.univ.filter (fun k : K => l ∈ A k)).card) →
      (∀ r : R,
        (Finset.univ.filter (fun e : E => right e = r)).card =
          (Finset.univ.filter (fun k : K => r ∈ B k)).card) →
      (∀ U : Finset L, ∀ V : Finset R,
        (Finset.univ.filter
          (fun e : E => left e ∈ U ∧ right e ∈ V)).card
          ≤ ∑ k : K, min ((A k ∩ U).card) ((B k ∩ V).card)) →
      ∃ κ : E → K,
        (∀ e : E, left e ∈ A (κ e) ∧ right e ∈ B (κ e)) ∧
        (∀ l : L, ∀ k : K, l ∈ A k →
          ∃! e : E, left e = l ∧ κ e = k) ∧
        (∀ r : R, ∀ k : K, r ∈ B k →
          ∃! e : E, right e = r ∧ κ e = k)
```

For the current theorem, take `L := C`, `R := Fin T`, `K := X`, `A := active`,
and `B x := Finset.univ`.  Then the rectangle condition becomes exactly your
hypothesis because `(Finset.univ ∩ S).card = S.card`.

The key adapter is the following.  It converts a compatible colouring
`κ : E → X` into the requested family of equivalences and proves the exact
`edgePairCount` equality by an explicit cardinal equivalence between colours
and copied edges in each cell `(c, σ)`.

```lean
lemma choiceDegree_eq_card_subtype
    {X C : Type*} [Fintype X] [DecidableEq X] [DecidableEq C]
    (f : X → C) (c : C) :
    Incidence.choiceDegree f c =
      Fintype.card {x : X // f x = c} := by
  classical
  simp [Incidence.choiceDegree]

lemma edgePairCount_eq_card_subtype
    {T : Nat} {C E : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq C]
    (left : E → C) (right : E → Fin T) (c : C) (σ : Fin T) :
    edgePairCount left right c σ =
      Fintype.card {e : E // left e = c ∧ right e = σ} := by
  classical
  simp [edgePairCount]

theorem compatibleColoring_to_exactEdgeColoring
    {T : Nat} {X C E : Type*}
    [Fintype X] [Fintype C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E]
    (left : E → C) (right : E → Fin T) (active : X → Finset C)
    (κ : E → X)
    (hκ : ∀ e : E, left e ∈ active (κ e))
    (hL : ∀ c : C, ∀ x : X, c ∈ active x →
      ∃! e : E, left e = c ∧ κ e = x)
    (hR : ∀ σ : Fin T, ∀ x : X,
      ∃! e : E, right e = σ ∧ κ e = x) :
    ∃ e : (∀ x : X, Fin T ≃ {c : C // c ∈ active x}),
      ∀ c : C, ∀ σ : Fin T,
        Incidence.choiceDegree (fun x : X => ((e x) σ).1) c =
          edgePairCount left right c σ := by
  classical

  let edgeAt : X → Fin T → E :=
    fun x σ => Classical.choose (hR σ x)

  have edgeAt_spec :
      ∀ x σ, right (edgeAt x σ) = σ ∧ κ (edgeAt x σ) = x := by
    intro x σ
    exact (Classical.choose_spec (hR σ x)).1

  have edgeAt_unique :
      ∀ {x σ} {e0 : E},
        right e0 = σ ∧ κ e0 = x → e0 = edgeAt x σ := by
    intro x σ e0 he
    exact (Classical.choose_spec (hR σ x)).2 e0 he

  let val : ∀ x : X, Fin T → {c : C // c ∈ active x} :=
    fun x σ =>
      ⟨left (edgeAt x σ), by
        have hx : κ (edgeAt x σ) = x := (edgeAt_spec x σ).2
        simpa [hx] using hκ (edgeAt x σ)⟩

  have val_inj : ∀ x : X, Function.Injective (val x) := by
    intro x σ τ hστ
    have hleft_eq : left (edgeAt x σ) = left (edgeAt x τ) := by
      exact congrArg Subtype.val hστ
    let c : C := left (edgeAt x σ)
    have hc : c ∈ active x := (val x σ).2
    obtain ⟨eL, heL, huniqL⟩ := hL c x hc
    have hσ : left (edgeAt x σ) = c ∧ κ (edgeAt x σ) = x := by
      exact ⟨rfl, (edgeAt_spec x σ).2⟩
    have hτ : left (edgeAt x τ) = c ∧ κ (edgeAt x τ) = x := by
      exact ⟨by simpa [c] using hleft_eq.symm, (edgeAt_spec x τ).2⟩
    have eσ : edgeAt x σ = eL := huniqL (edgeAt x σ) hσ
    have eτ : edgeAt x τ = eL := huniqL (edgeAt x τ) hτ
    have heq : edgeAt x σ = edgeAt x τ := eσ.trans eτ.symm
    calc
      σ = right (edgeAt x σ) := (edgeAt_spec x σ).1.symm
      _ = right (edgeAt x τ) := by rw [heq]
      _ = τ := (edgeAt_spec x τ).1

  have val_surj : ∀ x : X, Function.Surjective (val x) := by
    intro x y
    obtain ⟨eL, heL, huniqL⟩ := hL y.1 x y.2
    refine ⟨right eL, ?_⟩
    apply Subtype.ext
    have heq : eL = edgeAt x (right eL) :=
      edgeAt_unique (x := x) (σ := right eL) (e0 := eL)
        ⟨rfl, heL.2⟩
    rw [← heq]
    exact heL.1

  let ee : ∀ x : X, Fin T ≃ {c : C // c ∈ active x} :=
    fun x => Equiv.ofBijective (val x) ⟨val_inj x, val_surj x⟩

  have ee_apply :
      ∀ x σ, ((ee x) σ).1 = left (edgeAt x σ) := by
    intro x σ
    simp [ee, val]

  refine ⟨ee, ?_⟩
  intro c σ

  let cellEquiv :
      {x : X // ((ee x) σ).1 = c} ≃
        {e0 : E // left e0 = c ∧ right e0 = σ} :=
    {
      toFun := fun x =>
        ⟨edgeAt x.1 σ, by
          have hx : left (edgeAt x.1 σ) = c := by
            simpa [ee_apply x.1 σ] using x.2
          exact ⟨hx, (edgeAt_spec x.1 σ).1⟩⟩

      invFun := fun e0 =>
        ⟨κ e0.1, by
          have heq : e0.1 = edgeAt (κ e0.1) σ :=
            edgeAt_unique
              (x := κ e0.1) (σ := σ) (e0 := e0.1)
              ⟨e0.2.2, rfl⟩
          have hx : left (edgeAt (κ e0.1) σ) = c := by
            rw [← heq]
            exact e0.2.1
          simpa [ee_apply (κ e0.1) σ] using hx⟩

      left_inv := by
        intro x
        apply Subtype.ext
        change κ (edgeAt x.1 σ) = x.1
        exact (edgeAt_spec x.1 σ).2

      right_inv := by
        intro e0
        apply Subtype.ext
        change edgeAt (κ e0.1) σ = e0.1
        exact (edgeAt_unique
          (x := κ e0.1) (σ := σ) (e0 := e0.1)
          ⟨e0.2.2, rfl⟩).symm
    }

  calc
    Incidence.choiceDegree (fun x : X => ((ee x) σ).1) c
        = Fintype.card {x : X // ((ee x) σ).1 = c} :=
          choiceDegree_eq_card_subtype
            (fun x : X => ((ee x) σ).1) c
    _ = Fintype.card {e0 : E // left e0 = c ∧ right e0 = σ} :=
          Fintype.card_congr cellEquiv
    _ = edgePairCount left right c σ :=
          (edgePairCount_eq_card_subtype left right c σ).symm
```

Now the final adapter from the external theorem to your current goal is:

```lean
theorem exactEdgeColoringGoal_of_compatibleDeWerra
    (hDW : CompatibleDeWerraGoal) :
    ExactEdgeColoringGoal := by
  classical
  intro T X C E _ _ _ _ _ _
  intro left right active hActive hLeft hRight hRect

  let B : X → Finset (Fin T) := fun _ => Finset.univ

  have hcardDW : ∀ x : X, (active x).card = (B x).card := by
    intro x
    simpa [B] using hActive x

  have hleftDW :
      ∀ c : C,
        (Finset.univ.filter (fun e : E => left e = c)).card =
          (Finset.univ.filter (fun x : X => c ∈ active x)).card := by
    intro c
    simpa [edgeLeftDegree, activeDegree] using hLeft c

  have hrightDW :
      ∀ σ : Fin T,
        (Finset.univ.filter (fun e : E => right e = σ)).card =
          (Finset.univ.filter (fun x : X => σ ∈ B x)).card := by
    intro σ
    simpa [edgeRightDegree, B] using hRight σ

  have hrectDW :
      ∀ U : Finset C, ∀ S : Finset (Fin T),
        (Finset.univ.filter
          (fun e : E => left e ∈ U ∧ right e ∈ S)).card
          ≤ ∑ x : X, min ((active x ∩ U).card) ((B x ∩ S).card) := by
    intro U S
    simpa [edgeRectCount, B] using hRect U S

  obtain ⟨κ, hκ, hL, hR⟩ :=
    hDW
      (left := left)
      (right := right)
      (A := active)
      (B := B)
      hcardDW hleftDW hrightDW hrectDW

  exact compatibleColoring_to_exactEdgeColoring
    left right active κ
    (fun e => (hκ e).1)
    (fun c x hc => hL c x hc)
    (fun σ x => hR σ x (by simp [B]))
```

This proves the current `ExactEdgeColoringGoal` once `CompatibleDeWerraGoal` is available.  The pair-count preservation is not weakened: for each fixed `(c, σ)`, `cellEquiv` is an explicit equivalence between

```lean
{x : X // ((ee x) σ).1 = c}
```

and

```lean
{e : E // left e = c ∧ right e = σ}.
```

So the final equality is exactly the copied-edge count `edgePairCount left right c σ`.

If you prefer an internal induction proof instead of importing de Werra, the right hard lemma to isolate is the last-fibre split lemma:

```lean
def LastFiberSplitGoal : Prop :=
  ∀ {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (m : C → Fin (T + 1) → Nat) (active : X → Finset C),
      (∀ x, (active x).card = T + 1) →
      (∀ c, (∑ σ : Fin (T + 1), m c σ) = activeDegree active c) →
      (∀ σ, (∑ c : C, m c σ) = Fintype.card X) →
      (∀ U : Finset C, ∀ S : Finset (Fin (T + 1)),
        (∑ c in U, ∑ σ in S, m c σ)
          ≤ ∑ x : X, min ((active x ∩ U).card) S.card) →
      ∃ pick : X → C,
        (∀ x, pick x ∈ active x) ∧
        (∀ c, Incidence.choiceDegree pick c = m c (Fin.last T)) ∧
        (∀ U : Finset C, ∀ S : Finset (Fin T),
          (∑ c in U, ∑ σ in S, m c (Fin.castSucc σ))
            ≤ ∑ x : X,
                min ((((active x).erase (pick x)) ∩ U).card) S.card)
```

Then the induction on `T` is routine: erase `pick x` from each active set, recurse on the `Fin.castSucc` columns, and extend the equivalences by sending `Fin.last T` to `pick x`. The necessary elementary helpers are:

```lean
lemma activeDegree_erase_pick_add_choiceDegree
    {X C : Type*} [Fintype X] [DecidableEq X] [DecidableEq C]
    (active : X → Finset C) (pick : X → C)
    (hpick : ∀ x, pick x ∈ active x) (c : C) :
    activeDegree (fun x => (active x).erase (pick x)) c
      + Incidence.choiceDegree pick c =
    activeDegree active c
```

and an equivalence constructor

```lean
def finSuccSubtypeEraseEquiv
    {T : Nat} {C : Type*} [DecidableEq C]
    (A : Finset C) (a : C) (ha : a ∈ A)
    (e : Fin T ≃ {c : C // c ∈ A.erase a}) :
    Fin (T + 1) ≃ {c : C // c ∈ A}
```

with simp lemmas

```lean
@[simp] theorem finSuccSubtypeEraseEquiv_last_val :
  ((finSuccSubtypeEraseEquiv A a ha e) (Fin.last T)).1 = a

@[simp] theorem finSuccSubtypeEraseEquiv_castSucc_val (i : Fin T) :
  ((finSuccSubtypeEraseEquiv A a ha e) (Fin.castSucc i)).1 = (e i).1
```

But the shortest route for `ActiveHall.lean` is the de Werra adapter above.