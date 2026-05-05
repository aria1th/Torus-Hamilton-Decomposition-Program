import RoundComposite.ActiveHall

namespace RoundComposite
namespace ActiveHall
namespace FiniteHoffman

open scoped BigOperators

universe u uX uC

lemma exists_unique_one_of_sum_eq_one {α : Type u} [Fintype α]
    (z : α → Nat) (hz01 : ∀ a, z a ≤ 1)
    (hsum : (∑ a : α, z a) = 1) :
    ∃! a : α, z a = 1 := by
  classical
  have hex : ∃ a : α, z a = 1 := by
    by_contra hno
    have hzero : ∀ a : α, z a = 0 := by
      intro a
      have hne : z a ≠ 1 := by
        intro h
        exact hno ⟨a, h⟩
      have hzle := hz01 a
      omega
    have hsum0 : (∑ a : α, z a) = 0 := by
      simp [hzero]
    omega
  rcases hex with ⟨a, ha⟩
  refine ⟨a, ha, ?_⟩
  intro b hb
  by_contra hne
  have hle_two : 2 ≤ (∑ x : α, z x) := by
    let s : Finset α := {a, b}
    have hs_sub : s ⊆ (Finset.univ : Finset α) := by
      intro x _hx
      simp
    have hsum_s_le :
        (∑ x ∈ s, z x) ≤ ∑ x ∈ (Finset.univ : Finset α), z x := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hs_sub
        (by intro x _hxuniv _hxs; exact Nat.zero_le _)
    have hsum_s : (∑ x ∈ s, z x) = 2 := by
      have hab : a ≠ b := by
        exact fun h => hne h.symm
      rw [Finset.sum_pair (f := z) hab]
      rw [ha, hb]
    rw [hsum_s] at hsum_s_le
    simpa using hsum_s_le
  omega

lemma onehot_value_eq {α : Type u} [Fintype α]
    (z : α → Nat) (hz01 : ∀ a, z a ≤ 1)
    (hsum : (∑ a : α, z a) = 1) :
    z (Classical.choose (exists_unique_one_of_sum_eq_one z hz01 hsum).exists) = 1 := by
  classical
  exact Classical.choose_spec (exists_unique_one_of_sum_eq_one z hz01 hsum).exists

lemma onehot_eq_of_value_eq {α : Type u} [Fintype α]
    (z : α → Nat) (hz01 : ∀ a, z a ≤ 1)
    (hsum : (∑ a : α, z a) = 1)
    {a : α} (ha : z a = 1) :
    Classical.choose (exists_unique_one_of_sum_eq_one z hz01 hsum).exists = a := by
  classical
  let huniq := exists_unique_one_of_sum_eq_one z hz01 hsum
  exact huniq.unique (onehot_value_eq z hz01 hsum) ha

/--
Binary matrix form of the finite compatible de Werra edge-colouring theorem.
The hard theorem is the existence of `z`; extracting a colour function from
such a matrix is elementary and proved below.
-/
def CompatibleZeroOneMatrixGoal : Prop :=
  ∀ {L : Type uC} {R : Type} {K : Type uX} {E : Type uC}
    [Fintype L] [Fintype R] [Fintype K] [Fintype E]
    [DecidableEq L] [DecidableEq R] [DecidableEq K] [DecidableEq E],
    ∀ (left : E → L) (right : E → R)
      (A : K → Finset L) (B : K → Finset R),
      (∀ k : K, (A k).card = (B k).card) →
      (∀ l : L,
        ((Finset.univ : Finset E).filter (fun e => left e = l)).card =
          ((Finset.univ : Finset K).filter (fun k => l ∈ A k)).card) →
      (∀ r : R,
        ((Finset.univ : Finset E).filter (fun e => right e = r)).card =
          ((Finset.univ : Finset K).filter (fun k => r ∈ B k)).card) →
      (∀ U : Finset L, ∀ V : Finset R,
        ((Finset.univ : Finset E).filter
          (fun e => left e ∈ U ∧ right e ∈ V)).card
          ≤ ∑ k : K, min ((A k ∩ U).card) ((B k ∩ V).card)) →
      ∃ z : E → K → Nat,
        (∀ e k, z e k ≤ 1) ∧
        (∀ e, (∑ k : K, z e k) = 1) ∧
        (∀ e k, z e k = 1 → left e ∈ A k ∧ right e ∈ B k) ∧
        (∀ l k, l ∈ A k →
          (∑ e : E, if left e = l then z e k else 0) = 1) ∧
        (∀ r k, r ∈ B k →
          (∑ e : E, if right e = r then z e k else 0) = 1)

theorem compatibleDeWerraGoal_of_matrix
    (hMat : CompatibleZeroOneMatrixGoal.{uX, uC}) :
    CompatibleDeWerraGoal.{uX, uC} := by
  classical
  intro L R K E _instL _instR _instK _instE _decL _decR _decK _decE
    left right A B hAB hLeft hRight hRect
  rcases hMat left right A B hAB hLeft hRight hRect with
    ⟨z, hz01, hzRow, hzCompat, hzLeft, hzRight⟩
  let rowUnique : ∀ e : E, ∃! k : K, z e k = 1 := by
    intro e
    exact exists_unique_one_of_sum_eq_one (fun k : K => z e k)
      (hz01 e) (hzRow e)
  let κ : E → K := fun e =>
    Classical.choose (rowUnique e).exists
  have hκ_value : ∀ e : E, z e (κ e) = 1 := by
    intro e
    exact Classical.choose_spec (rowUnique e).exists
  have hκ_eq_of_value : ∀ e : E, ∀ k : K, z e k = 1 → κ e = k := by
    intro e k hk
    exact (rowUnique e).unique (hκ_value e) hk
  refine ⟨κ, ?_, ?_, ?_⟩
  · intro e
    exact hzCompat e (κ e) (hκ_value e)
  · intro l k hlA
    let slot : E → Nat := fun e => if left e = l then z e k else 0
    have hslot01 : ∀ e : E, slot e ≤ 1 := by
      intro e
      dsimp [slot]
      by_cases hleq : left e = l
      · simp [hleq, hz01 e k]
      · simp [hleq]
    have hslotSum : (∑ e : E, slot e) = 1 := by
      simpa [slot] using hzLeft l k hlA
    let slotUnique : ∃! e : E, slot e = 1 :=
      exists_unique_one_of_sum_eq_one slot hslot01 hslotSum
    let e0 : E := Classical.choose slotUnique.exists
    have he0slot : slot e0 = 1 := Classical.choose_spec slotUnique.exists
    have he0left : left e0 = l := by
      by_contra hne
      have : slot e0 = 0 := by simp [slot, hne]
      omega
    have he0zk : z e0 k = 1 := by
      simpa [slot, he0left] using he0slot
    refine ⟨e0, ?_, ?_⟩
    · exact ⟨he0left, hκ_eq_of_value e0 k he0zk⟩
    · intro e he
      have hslot_e : slot e = 1 := by
        have hzk : z e k = 1 := by
          have hv := hκ_value e
          simpa [he.2] using hv
        simpa [slot, he.1] using hzk
      exact (slotUnique.unique he0slot hslot_e).symm
  · intro r k hrB
    let slot : E → Nat := fun e => if right e = r then z e k else 0
    have hslot01 : ∀ e : E, slot e ≤ 1 := by
      intro e
      dsimp [slot]
      by_cases hreq : right e = r
      · simp [hreq, hz01 e k]
      · simp [hreq]
    have hslotSum : (∑ e : E, slot e) = 1 := by
      simpa [slot] using hzRight r k hrB
    let slotUnique : ∃! e : E, slot e = 1 :=
      exists_unique_one_of_sum_eq_one slot hslot01 hslotSum
    let e0 : E := Classical.choose slotUnique.exists
    have he0slot : slot e0 = 1 := Classical.choose_spec slotUnique.exists
    have he0right : right e0 = r := by
      by_contra hne
      have : slot e0 = 0 := by simp [slot, hne]
      omega
    have he0zk : z e0 k = 1 := by
      simpa [slot, he0right] using he0slot
    refine ⟨e0, ?_, ?_⟩
    · exact ⟨he0right, hκ_eq_of_value e0 k he0zk⟩
    · intro e he
      have hslot_e : slot e = 1 := by
        have hzk : z e k = 1 := by
          have hv := hκ_value e
          simpa [he.2] using hv
        simpa [slot, he.1] using hzk
      exact (slotUnique.unique he0slot hslot_e).symm

theorem compatibleZeroOneMatrixGoal_of_compatibleDeWerraGoal
    (hDW : CompatibleDeWerraGoal.{uX, uC}) :
    CompatibleZeroOneMatrixGoal.{uX, uC} := by
  classical
  intro L R K E _instL _instR _instK _instE _decL _decR _decK _decE
    left right A B hAB hLeft hRight hRect
  rcases hDW left right A B hAB hLeft hRight hRect with
    ⟨κ, hκCompat, hκLeft, hκRight⟩
  let z : E → K → Nat := fun e k => if κ e = k then 1 else 0
  refine ⟨z, ?_, ?_, ?_, ?_, ?_⟩
  · intro e k
    dsimp [z]
    by_cases h : κ e = k <;> simp [h]
  · intro e
    dsimp [z]
    rw [Finset.sum_eq_single (κ e)]
    · simp
    · intro k _hk hne
      simp [hne.symm]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ (κ e)))
  · intro e k hzek
    have hk : κ e = k := by
      dsimp [z] at hzek
      by_contra hne
      simp [hne] at hzek
    rw [← hk]
    exact hκCompat e
  · intro l k hlA
    rcases hκLeft l k hlA with ⟨e0, he0, huniq⟩
    dsimp [z]
    rw [Finset.sum_eq_single e0]
    · simp [he0.1, he0.2]
    · intro e _he hne
      have hnot : ¬ (left e = l ∧ κ e = k) := by
        intro h
        exact hne (huniq e h)
      by_cases hl : left e = l
      · have hk : κ e ≠ k := by
          intro hk
          exact hnot ⟨hl, hk⟩
        simp [hl, hk]
      · simp [hl]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ e0))
  · intro r k hrB
    rcases hκRight r k hrB with ⟨e0, he0, huniq⟩
    dsimp [z]
    rw [Finset.sum_eq_single e0]
    · simp [he0.1, he0.2]
    · intro e _he hne
      have hnot : ¬ (right e = r ∧ κ e = k) := by
        intro h
        exact hne (huniq e h)
      by_cases hr : right e = r
      · have hk : κ e ≠ k := by
          intro hk
          exact hnot ⟨hr, hk⟩
        simp [hr, hk]
      · simp [hr]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ e0))

theorem compatibleZeroOneMatrixGoal_iff_compatibleDeWerraGoal :
    CompatibleZeroOneMatrixGoal.{uX, uC} ↔ CompatibleDeWerraGoal.{uX, uC} :=
  ⟨compatibleDeWerraGoal_of_matrix,
    compatibleZeroOneMatrixGoal_of_compatibleDeWerraGoal⟩

/--
A finite obstruction to the unrestricted two-sided compatible de Werra
endpoint.

The graph is the `3 × 3` bipartite graph with the diagonal removed.  The three
listed colours satisfy all degree and rectangle-cut hypotheses, but the forced
edge `(0, 1)` makes colour `1` unavailable for `(0, 2)`, while the alternative
colour `0` is already forced at right endpoint `2`.
-/
theorem not_compatibleDeWerraGoal :
    ¬ CompatibleDeWerraGoal.{0, 0} := by
  classical
  intro hDW
  let left : Fin 6 → Fin 3 := fun e =>
    if e = 0 then 0 else
    if e = 1 then 0 else
    if e = 2 then 1 else
    if e = 3 then 1 else
    if e = 4 then 2 else
      2
  let right : Fin 6 → Fin 3 := fun e =>
    if e = 0 then 1 else
    if e = 1 then 2 else
    if e = 2 then 0 else
    if e = 3 then 2 else
    if e = 4 then 0 else
      1
  let A : Fin 3 → Finset (Fin 3) := fun k =>
    if k = 0 then ({0, 1} : Finset (Fin 3)) else
    if k = 1 then ({0, 2} : Finset (Fin 3)) else
      ({1, 2} : Finset (Fin 3))
  let B : Fin 3 → Finset (Fin 3) := fun k =>
    if k = 0 then ({0, 2} : Finset (Fin 3)) else
    if k = 1 then ({1, 2} : Finset (Fin 3)) else
      ({0, 1} : Finset (Fin 3))
  have hCard : ∀ k : Fin 3, (A k).card = (B k).card := by
    decide
  have hLeft :
      ∀ l : Fin 3,
        ((Finset.univ : Finset (Fin 6)).filter
          (fun e => left e = l)).card =
          ((Finset.univ : Finset (Fin 3)).filter
            (fun k => l ∈ A k)).card := by
    decide
  have hRight :
      ∀ r : Fin 3,
        ((Finset.univ : Finset (Fin 6)).filter
          (fun e => right e = r)).card =
          ((Finset.univ : Finset (Fin 3)).filter
            (fun k => r ∈ B k)).card := by
    decide
  have hRect :
      ∀ U : Finset (Fin 3), ∀ V : Finset (Fin 3),
        ((Finset.univ : Finset (Fin 6)).filter
          (fun e => left e ∈ U ∧ right e ∈ V)).card
          ≤ ∑ k : Fin 3, min ((A k ∩ U).card) ((B k ∩ V).card) := by
    decide
  rcases hDW (left := left) (right := right) (A := A) (B := B)
      hCard hLeft hRight hRect with
    ⟨κ, hκ, hκLeft, hκRight⟩
  have hκ0 : κ 0 = 1 := by
    let k : Fin 3 := κ 0
    have hkdef : k = κ 0 := rfl
    have h : left 0 ∈ A k ∧ right 0 ∈ B k := by
      simpa [k] using hκ 0
    have hk : k = 1 := by
      have hcases : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by
        omega
      rcases hcases with hk0 | hk1 | hk2
      · have hk0' : k = 0 := Fin.ext hk0
        exfalso
        simp [left, right, A, B, hk0'] at h
      · exact Fin.ext hk1
      · have hk2' : k = 2 := Fin.ext hk2
        exfalso
        simp [left, right, A, B, hk2'] at h
    exact hkdef.symm.trans hk
  have hκ3 : κ 3 = 0 := by
    let k : Fin 3 := κ 3
    have hkdef : k = κ 3 := rfl
    have h : left 3 ∈ A k ∧ right 3 ∈ B k := by
      simpa [k] using hκ 3
    have hk : k = 0 := by
      have hcases : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by
        omega
      rcases hcases with hk0 | hk1 | hk2
      · exact Fin.ext hk0
      · have hk1' : k = 1 := Fin.ext hk1
        exfalso
        simp [left, right, A, B, hk1'] at h
      · have hk2' : k = 2 := Fin.ext hk2
        exfalso
        simp [left, right, A, B, hk2'] at h
    exact hkdef.symm.trans hk
  have hκ1_cases : κ 1 = 0 ∨ κ 1 = 1 := by
    let k : Fin 3 := κ 1
    have hkdef : k = κ 1 := rfl
    have h : left 1 ∈ A k ∧ right 1 ∈ B k := by
      simpa [k] using hκ 1
    have hk : k = 0 ∨ k = 1 := by
      have hcases : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by
        omega
      rcases hcases with hk0 | hk1 | hk2
      · exact Or.inl (Fin.ext hk0)
      · exact Or.inr (Fin.ext hk1)
      · have hk2' : k = 2 := Fin.ext hk2
        exfalso
        simp [left, right, A, B, hk2'] at h
    exact hk.imp (fun h0 => hkdef.symm.trans h0)
      (fun h1 => hkdef.symm.trans h1)
  rcases hκ1_cases with hκ1 | hκ1
  · have h13 : right (1 : Fin 6) = 2 ∧ κ (1 : Fin 6) = 0 := by
      exact ⟨by decide, hκ1⟩
    have h33 : right (3 : Fin 6) = 2 ∧ κ (3 : Fin 6) = 0 := by
      exact ⟨by decide, hκ3⟩
    have heq : (1 : Fin 6) = 3 :=
      (hκRight 2 0 (by decide)).unique h13 h33
    have hval := congrArg Fin.val heq
    norm_num at hval
  · have h01 : left (0 : Fin 6) = 0 ∧ κ (0 : Fin 6) = 1 := by
      exact ⟨by decide, hκ0⟩
    have h11 : left (1 : Fin 6) = 0 ∧ κ (1 : Fin 6) = 1 := by
      exact ⟨by decide, hκ1⟩
    have heq : (0 : Fin 6) = 1 :=
      (hκLeft 0 1 (by decide)).unique h01 h11
    have hval := congrArg Fin.val heq
    norm_num at hval

theorem not_compatibleZeroOneMatrixGoal :
    ¬ CompatibleZeroOneMatrixGoal.{0, 0} := by
  intro hMat
  exact not_compatibleDeWerraGoal
    (compatibleDeWerraGoal_of_matrix hMat)

theorem rawExactEdgeColoringGoal_of_matrix
    (hMat : CompatibleZeroOneMatrixGoal.{uX, uC}) :
    RawExactEdgeColoringGoal.{uX, uC} :=
  rawExactEdgeColoringGoal_of_compatibleDeWerra
    (compatibleDeWerraGoal_of_matrix hMat)

/--
Copied-edge zero-one matrix form.  This is the direct matrix version of
`RawExactEdgeColoringGoal`; it avoids the extra right-allowed-set generality of
compatible de Werra.
-/
def RawZeroOneMatrixGoal : Prop :=
  ∀ {T : Nat} {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Fintype C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E],
    ∀ (left : E → C) (right : E → Fin T) (active : X → Finset C),
      (∀ x : X, (active x).card = T) →
      (∀ c : C, edgeLeftDegree left c = activeDegree active c) →
      (∀ σ : Fin T, edgeRightDegree right σ = Fintype.card X) →
      (∀ U : Finset C, ∀ S : Finset (Fin T),
        edgeRectCount left right U S
          ≤ ∑ x : X, min ((active x ∩ U).card) S.card) →
      ∃ z : E → X → Nat,
        (∀ e x, z e x ≤ 1) ∧
        (∀ e, (∑ x : X, z e x) = 1) ∧
        (∀ e x, z e x = 1 → left e ∈ active x) ∧
        (∀ x σ, (∑ e : E, if right e = σ then z e x else 0) = 1) ∧
        (∀ x c, c ∈ active x →
          (∑ e : E, if left e = c then z e x else 0) = 1)

theorem rawZeroOneMatrix_zero
    {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E]
    (left : E → C) (right : E → Fin 0) (active : X → Finset C)
    (hActive : ∀ x : X, (active x).card = 0)
    (_hLeft : ∀ c : C, edgeLeftDegree left c = activeDegree active c)
    (_hRight : ∀ σ : Fin 0, edgeRightDegree right σ = Fintype.card X)
    (_hRect : ∀ U : Finset C, ∀ S : Finset (Fin 0),
      edgeRectCount left right U S
        ≤ ∑ x : X, min ((active x ∩ U).card) S.card) :
    ∃ z : E → X → Nat,
      (∀ e x, z e x ≤ 1) ∧
      (∀ e, (∑ x : X, z e x) = 1) ∧
      (∀ e x, z e x = 1 → left e ∈ active x) ∧
      (∀ x σ, (∑ e : E, if right e = σ then z e x else 0) = 1) ∧
      (∀ x c, c ∈ active x →
        (∑ e : E, if left e = c then z e x else 0) = 1) := by
  classical
  let z : E → X → Nat := fun _ _ => 0
  refine ⟨z, ?_, ?_, ?_, ?_, ?_⟩
  · intro e x
    simp [z]
  · intro e
    exact Fin.elim0 (right e)
  · intro e x hz
    simp [z] at hz
  · intro x σ
    exact Fin.elim0 σ
  · intro x c hc
    have hEmpty : active x = ∅ :=
      Finset.card_eq_zero.mp (hActive x)
    have hcEmpty : c ∈ (∅ : Finset C) := hEmpty ▸ hc
    simp at hcEmpty

theorem rawExactEdgeColoringGoal_of_rawMatrix
    (hMat : RawZeroOneMatrixGoal.{uX, uC}) :
    RawExactEdgeColoringGoal.{uX, uC} := by
  classical
  intro T X C E _instX _instC _instE _decX _decC _decE
    left right active hActive hLeft hRight hRect
  rcases hMat left right active hActive hLeft hRight hRect with
    ⟨z, hz01, hzRow, hzActive, hzRight, hzLeft⟩
  let rowUnique : ∀ e : E, ∃! x : X, z e x = 1 := by
    intro e
    exact exists_unique_one_of_sum_eq_one (fun x : X => z e x)
      (hz01 e) (hzRow e)
  let κ : E → X := fun e =>
    Classical.choose (rowUnique e).exists
  have hκ_value : ∀ e : E, z e (κ e) = 1 := by
    intro e
    exact Classical.choose_spec (rowUnique e).exists
  have hκ_eq_of_value : ∀ e : E, ∀ x : X, z e x = 1 → κ e = x := by
    intro e x hx
    exact (rowUnique e).unique (hκ_value e) hx
  refine ⟨κ, ?_, ?_, ?_⟩
  · intro e
    exact hzActive e (κ e) (hκ_value e)
  · intro x σ
    let slot : E → Nat := fun e => if right e = σ then z e x else 0
    have hslot01 : ∀ e : E, slot e ≤ 1 := by
      intro e
      dsimp [slot]
      by_cases hreq : right e = σ
      · simp [hreq, hz01 e x]
      · simp [hreq]
    have hslotSum : (∑ e : E, slot e) = 1 := by
      simpa [slot] using hzRight x σ
    let slotUnique : ∃! e : E, slot e = 1 :=
      exists_unique_one_of_sum_eq_one slot hslot01 hslotSum
    let e0 : E := Classical.choose slotUnique.exists
    have he0slot : slot e0 = 1 := Classical.choose_spec slotUnique.exists
    have he0right : right e0 = σ := by
      by_contra hne
      have : slot e0 = 0 := by simp [slot, hne]
      omega
    have he0zx : z e0 x = 1 := by
      simpa [slot, he0right] using he0slot
    refine ⟨e0, ?_, ?_⟩
    · exact ⟨hκ_eq_of_value e0 x he0zx, he0right⟩
    · intro e he
      have hslot_e : slot e = 1 := by
        have hzex : z e x = 1 := by
          have hv := hκ_value e
          simpa [he.1] using hv
        simpa [slot, he.2] using hzex
      exact (slotUnique.unique he0slot hslot_e).symm
  · intro x c hc
    let slot : E → Nat := fun e => if left e = c then z e x else 0
    have hslot01 : ∀ e : E, slot e ≤ 1 := by
      intro e
      dsimp [slot]
      by_cases hleq : left e = c
      · simp [hleq, hz01 e x]
      · simp [hleq]
    have hslotSum : (∑ e : E, slot e) = 1 := by
      simpa [slot] using hzLeft x c hc
    let slotUnique : ∃! e : E, slot e = 1 :=
      exists_unique_one_of_sum_eq_one slot hslot01 hslotSum
    let e0 : E := Classical.choose slotUnique.exists
    have he0slot : slot e0 = 1 := Classical.choose_spec slotUnique.exists
    have he0left : left e0 = c := by
      by_contra hne
      have : slot e0 = 0 := by simp [slot, hne]
      omega
    have he0zx : z e0 x = 1 := by
      simpa [slot, he0left] using he0slot
    refine ⟨e0, ?_, ?_⟩
    · exact ⟨hκ_eq_of_value e0 x he0zx, he0left⟩
    · intro e he
      have hslot_e : slot e = 1 := by
        have hzex : z e x = 1 := by
          have hv := hκ_value e
          simpa [he.1] using hv
        simpa [slot, he.2] using hzex
      exact (slotUnique.unique he0slot hslot_e).symm

theorem rawZeroOneMatrix_of_rawExactWitness
    {T : Nat} {X : Type uX} {C E : Type uC}
    [Fintype X] [Fintype E]
    [DecidableEq C]
    (left : E → C) (right : E → Fin T) (active : X → Finset C)
    (κ : E → X)
    (hκActive : ∀ e : E, left e ∈ active (κ e))
    (hκRight : ∀ x : X, ∀ σ : Fin T,
      ∃! e : E, κ e = x ∧ right e = σ)
    (hκLeft : ∀ x : X, ∀ c : C, c ∈ active x →
      ∃! e : E, κ e = x ∧ left e = c) :
    ∃ z : E → X → Nat,
      (∀ e x, z e x ≤ 1) ∧
      (∀ e, (∑ x : X, z e x) = 1) ∧
      (∀ e x, z e x = 1 → left e ∈ active x) ∧
      (∀ x σ, (∑ e : E, if right e = σ then z e x else 0) = 1) ∧
      (∀ x c, c ∈ active x →
        (∑ e : E, if left e = c then z e x else 0) = 1) := by
  classical
  let z : E → X → Nat := fun e x => if κ e = x then 1 else 0
  refine ⟨z, ?_, ?_, ?_, ?_, ?_⟩
  · intro e x
    dsimp [z]
    by_cases h : κ e = x <;> simp [h]
  · intro e
    dsimp [z]
    rw [Finset.sum_eq_single (κ e)]
    · simp
    · intro x _hx hne
      simp [hne.symm]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ (κ e)))
  · intro e x hx
    have hk : κ e = x := by
      dsimp [z] at hx
      by_contra hne
      simp [hne] at hx
    rw [← hk]
    exact hκActive e
  · intro x σ
    rcases hκRight x σ with ⟨e0, he0, huniq⟩
    dsimp [z]
    rw [Finset.sum_eq_single e0]
    · simp [he0.1, he0.2]
    · intro e _he hne
      have hnot : ¬ (right e = σ ∧ κ e = x) := by
        intro h
        exact hne (huniq e ⟨h.2, h.1⟩)
      by_cases hr : right e = σ
      · have hk : κ e ≠ x := by
          intro hk
          exact hnot ⟨hr, hk⟩
        simp [hr, hk]
      · simp [hr]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ e0))
  · intro x c hc
    rcases hκLeft x c hc with ⟨e0, he0, huniq⟩
    dsimp [z]
    rw [Finset.sum_eq_single e0]
    · simp [he0.1, he0.2]
    · intro e _he hne
      have hnot : ¬ (left e = c ∧ κ e = x) := by
        intro h
        exact hne (huniq e ⟨h.2, h.1⟩)
      by_cases hl : left e = c
      · have hk : κ e ≠ x := by
          intro hk
          exact hnot ⟨hl, hk⟩
        simp [hl, hk]
      · simp [hl]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ e0))

theorem rawZeroOneMatrixGoal_of_rawExactEdgeColoringGoal
    (hRaw : RawExactEdgeColoringGoal.{uX, uC}) :
    RawZeroOneMatrixGoal.{uX, uC} := by
  classical
  intro T X C E _instX _instC _instE _decX _decC _decE
    left right active hActive hLeft hRight hRect
  rcases hRaw left right active hActive hLeft hRight hRect with
    ⟨κ, hκActive, hκRight, hκLeft⟩
  exact rawZeroOneMatrix_of_rawExactWitness
    left right active κ hκActive hκRight hκLeft

theorem rawZeroOneMatrixGoal_iff_rawExactEdgeColoringGoal :
    RawZeroOneMatrixGoal.{uX, uC} ↔ RawExactEdgeColoringGoal.{uX, uC} :=
  ⟨rawExactEdgeColoringGoal_of_rawMatrix,
    rawZeroOneMatrixGoal_of_rawExactEdgeColoringGoal⟩

theorem rawZeroOneMatrixGoal_of_compatibleZeroOneMatrixGoal
    (hMat : CompatibleZeroOneMatrixGoal.{uX, uC}) :
    RawZeroOneMatrixGoal.{uX, uC} :=
  rawZeroOneMatrixGoal_of_rawExactEdgeColoringGoal
    (rawExactEdgeColoringGoal_of_matrix hMat)

theorem rawZeroOneMatrixGoal_of_compatibleDeWerraGoal
    (hDW : CompatibleDeWerraGoal.{uX, uC}) :
    RawZeroOneMatrixGoal.{uX, uC} :=
  rawZeroOneMatrixGoal_of_compatibleZeroOneMatrixGoal
    (compatibleZeroOneMatrixGoal_of_compatibleDeWerraGoal hDW)

theorem rawExactEdgeColoring_of_exactWitness
    {T : Nat} {X : Type uX} {C E : Type uC}
    [Fintype X] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E]
    (left : E → C) (right : E → Fin T) (active : X → Finset C)
    (η : ∀ x : X, Fin T ≃ {c : C // c ∈ active x})
    (hη : ∀ c : C, ∀ σ : Fin T,
      Incidence.choiceDegree (fun x : X => ((η x) σ).1) c =
        edgePairCount left right c σ) :
    ∃ κ : E → X,
      (∀ e : E, left e ∈ active (κ e)) ∧
      (∀ x : X, ∀ σ : Fin T,
        ∃! e : E, κ e = x ∧ right e = σ) ∧
      (∀ x : X, ∀ c : C, c ∈ active x →
        ∃! e : E, κ e = x ∧ left e = c) := by
  classical
  let XSlot (c : C) (σ : Fin T) :=
    {x : X // ((η x) σ).1 = c}
  let EdgeSlot (c : C) (σ : Fin T) :=
    {e : E // left e = c ∧ right e = σ}
  have hslot_card :
      ∀ c : C, ∀ σ : Fin T,
        Fintype.card (XSlot c σ) = Fintype.card (EdgeSlot c σ) := by
    intro c σ
    dsimp [XSlot, EdgeSlot]
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa [Incidence.choiceDegree, edgePairCount] using hη c σ
  let slotEquiv : ∀ c : C, ∀ σ : Fin T, XSlot c σ ≃ EdgeSlot c σ :=
    fun c σ => Fintype.equivOfCardEq (hslot_card c σ)
  let κ : E → X := fun e =>
    ((slotEquiv (left e) (right e)).symm
      ⟨e, by simp⟩).1
  have hκ_slot :
      ∀ e : E, ((η (κ e)) (right e)).1 = left e := by
    intro e
    exact ((slotEquiv (left e) (right e)).symm
      ⟨e, by simp⟩).2
  have hκ_eq_of_slot :
      ∀ c : C, ∀ σ : Fin T, ∀ es : EdgeSlot c σ,
        κ es.1 = ((slotEquiv c σ).symm es).1 := by
    intro c σ es
    rcases es with ⟨e, hleft, hright⟩
    dsimp [κ, EdgeSlot] at *
    subst c
    subst σ
    rfl
  refine ⟨κ, ?_, ?_, ?_⟩
  · intro e
    have hmem := ((η (κ e)) (right e)).2
    simpa [hκ_slot e] using hmem
  · intro x σ
    let c : C := ((η x) σ).1
    let xs : XSlot c σ := ⟨x, rfl⟩
    let es : EdgeSlot c σ := slotEquiv c σ xs
    refine ⟨es.1, ?_, ?_⟩
    · have hright : right es.1 = σ := es.2.2
      have hx :
          ((slotEquiv c σ).symm es).1 = x := by
        have hxs : (slotEquiv c σ).symm (slotEquiv c σ xs) = xs :=
          (slotEquiv c σ).left_inv xs
        exact congrArg Subtype.val hxs
      have hκ : κ es.1 = x := by
        rw [hκ_eq_of_slot c σ es]
        exact hx
      exact ⟨hκ, hright⟩
    · intro e he
      have hleft : left e = c := by
        have hslot := hκ_slot e
        rw [he.1, he.2] at hslot
        exact hslot.symm
      have hedge :
          (⟨e, ⟨hleft, he.2⟩⟩ : EdgeSlot c σ) = es := by
        have hpre :
            (slotEquiv c σ).symm ⟨e, ⟨hleft, he.2⟩⟩ = xs := by
          apply Subtype.ext
          rw [← hκ_eq_of_slot c σ ⟨e, ⟨hleft, he.2⟩⟩]
          exact he.1
        have hpost := congrArg (slotEquiv c σ) hpre
        simpa [xs, es] using hpost
      exact Subtype.ext_iff.mp hedge
  · intro x c hc
    let σ : Fin T := (η x).symm ⟨c, hc⟩
    have hησ : ((η x) σ).1 = c := by
      dsimp [σ]
      simp
    let xs : XSlot c σ := ⟨x, hησ⟩
    let es : EdgeSlot c σ := slotEquiv c σ xs
    refine ⟨es.1, ?_, ?_⟩
    · have hleft : left es.1 = c := es.2.1
      have hx :
          ((slotEquiv c σ).symm es).1 = x := by
        have hxs : (slotEquiv c σ).symm (slotEquiv c σ xs) = xs :=
          (slotEquiv c σ).left_inv xs
        exact congrArg Subtype.val hxs
      have hκ : κ es.1 = x := by
        rw [hκ_eq_of_slot c σ es]
        exact hx
      exact ⟨hκ, hleft⟩
    · intro e he
      have hright : right e = σ := by
        have hslot := hκ_slot e
        rw [he.1, he.2] at hslot
        have hsub :
            (η x) (right e) = ⟨c, hc⟩ := by
          apply Subtype.ext
          simpa [he.2] using hslot
        have hsym := congrArg (η x).symm hsub
        simpa [σ] using hsym
      have hedge :
          (⟨e, ⟨he.2, hright⟩⟩ : EdgeSlot c σ) = es := by
        have hpre :
            (slotEquiv c σ).symm ⟨e, ⟨he.2, hright⟩⟩ = xs := by
          apply Subtype.ext
          rw [← hκ_eq_of_slot c σ ⟨e, ⟨he.2, hright⟩⟩]
          exact he.1
        have hpost := congrArg (slotEquiv c σ) hpre
        simpa [xs, es] using hpost
      exact Subtype.ext_iff.mp hedge

/--
The ordered SDR form and the copied-edge raw form are equivalent.  This
direction reconstructs an edge colouring by matching, for every pair `(c, σ)`,
the vertices whose local ordered choice at `σ` is `c` with the copied edges
whose endpoints are `(c, σ)`.
-/
theorem rawExactEdgeColoringGoal_of_exactEdgeColoringGoal
    (hExact : ExactEdgeColoringGoal.{uX, uC}) :
    RawExactEdgeColoringGoal.{uX, uC} := by
  classical
  intro T X C E _instX _instC _instE _decX _decC _decE
    left right active hActive hLeft hRight hRect
  rcases hExact left right active hActive hLeft hRight hRect with
    ⟨η, hη⟩
  exact rawExactEdgeColoring_of_exactWitness left right active η hη

theorem rawExactEdgeColoringGoal_iff_exactEdgeColoringGoal :
    RawExactEdgeColoringGoal.{uX, uC} ↔ ExactEdgeColoringGoal.{uX, uC} :=
  ⟨exactEdgeColoringGoal_of_raw,
    rawExactEdgeColoringGoal_of_exactEdgeColoringGoal⟩

theorem edgeLeftDegree_eq_sum_edgePairCount
    {T : Nat} {C E : Type uC} [Fintype E] [DecidableEq C]
    [DecidableEq E] (left : E → C) (right : E → Fin T) (c : C) :
    edgeLeftDegree left c =
      ∑ σ : Fin T, edgePairCount left right c σ := by
  classical
  rw [edgeLeftDegree]
  rw [← Fintype.card_subtype (fun e : E => left e = c)]
  let f :
      {e : E // left e = c} ≃
        Sigma fun σ : Fin T =>
          {e : E // left e = c ∧ right e = σ} :=
    { toFun := fun e => ⟨right e.1, ⟨e.1, ⟨e.2, rfl⟩⟩⟩
      invFun := fun q => ⟨q.2.1, q.2.2.1⟩
      left_inv := by
        intro e
        rfl
      right_inv := by
        intro q
        rcases q with ⟨σ, e, hleft, hright⟩
        subst σ
        rfl }
  calc
    Fintype.card {e : E // left e = c}
        =
        Fintype.card
          (Sigma fun σ : Fin T =>
            {e : E // left e = c ∧ right e = σ}) :=
          Fintype.card_congr f
    _ = ∑ σ : Fin T,
          Fintype.card {e : E // left e = c ∧ right e = σ} := by
          simp [Fintype.card_sigma]
    _ = ∑ σ : Fin T, edgePairCount left right c σ := by
          apply Finset.sum_congr rfl
          intro σ _hσ
          rw [edgePairCount]
          rw [← Fintype.card_subtype
            (fun e : E => left e = c ∧ right e = σ)]

theorem edgeRightDegree_eq_sum_edgePairCount
    {T : Nat} {C E : Type uC} [Fintype C] [Fintype E]
    [DecidableEq C] [DecidableEq E]
    (left : E → C) (right : E → Fin T) (σ : Fin T) :
    edgeRightDegree right σ =
      ∑ c : C, edgePairCount left right c σ := by
  classical
  rw [edgeRightDegree]
  rw [← Fintype.card_subtype (fun e : E => right e = σ)]
  let f :
      {e : E // right e = σ} ≃
        Sigma fun c : C =>
          {e : E // left e = c ∧ right e = σ} :=
    { toFun := fun e => ⟨left e.1, ⟨e.1, ⟨rfl, e.2⟩⟩⟩
      invFun := fun q => ⟨q.2.1, q.2.2.2⟩
      left_inv := by
        intro e
        rfl
      right_inv := by
        intro q
        rcases q with ⟨c, e, hleft, hright⟩
        subst c
        rfl }
  calc
    Fintype.card {e : E // right e = σ}
        =
        Fintype.card
          (Sigma fun c : C =>
            {e : E // left e = c ∧ right e = σ}) :=
          Fintype.card_congr f
    _ = ∑ c : C,
          Fintype.card {e : E // left e = c ∧ right e = σ} := by
          simp [Fintype.card_sigma]
    _ = ∑ c : C, edgePairCount left right c σ := by
          apply Finset.sum_congr rfl
          intro c _hc
          rw [edgePairCount]
          rw [← Fintype.card_subtype
            (fun e : E => left e = c ∧ right e = σ)]

theorem edgeRectCount_eq_sum_edgePairCount
    {T : Nat} {C E : Type uC} [Fintype E] [DecidableEq C]
    [DecidableEq E] (left : E → C) (right : E → Fin T)
    (U : Finset C) (S : Finset (Fin T)) :
    edgeRectCount left right U S =
      ∑ c ∈ U, ∑ σ ∈ S, edgePairCount left right c σ := by
  classical
  rw [edgeRectCount]
  rw [← Fintype.card_subtype
    (fun e : E => left e ∈ U ∧ right e ∈ S)]
  let f :
      {e : E // left e ∈ U ∧ right e ∈ S} ≃
        Sigma fun c : {c : C // c ∈ U} =>
          Sigma fun σ : {σ : Fin T // σ ∈ S} =>
            {e : E // left e = c.1 ∧ right e = σ.1} :=
    { toFun := fun e =>
        ⟨⟨left e.1, e.2.1⟩, ⟨⟨right e.1, e.2.2⟩,
          ⟨e.1, ⟨rfl, rfl⟩⟩⟩⟩
      invFun := fun q =>
        ⟨q.2.2.1, by
          exact ⟨by rw [q.2.2.2.1]; exact q.1.2,
            by rw [q.2.2.2.2]; exact q.2.1.2⟩⟩
      left_inv := by
        intro e
        rfl
      right_inv := by
        intro q
        rcases q with ⟨⟨c, hcU⟩, ⟨⟨σ, hσS⟩, e, hleft, hright⟩⟩
        symm at hleft
        change c = left e at hleft
        subst c
        symm at hright
        change σ = right e at hright
        subst σ
        rfl }
  calc
    Fintype.card {e : E // left e ∈ U ∧ right e ∈ S}
        =
        Fintype.card
          (Sigma fun c : {c : C // c ∈ U} =>
            Sigma fun σ : {σ : Fin T // σ ∈ S} =>
              {e : E // left e = c.1 ∧ right e = σ.1}) :=
          Fintype.card_congr f
    _ =
        ∑ c : {c : C // c ∈ U},
          ∑ σ : {σ : Fin T // σ ∈ S},
            Fintype.card {e : E // left e = c.1 ∧ right e = σ.1} := by
          simp [Fintype.card_sigma]
    _ = ∑ c ∈ U, ∑ σ ∈ S, edgePairCount left right c σ := by
          change
            (∑ c ∈ U.attach, ∑ σ ∈ S.attach,
              Fintype.card {e : E // left e = c.1 ∧ right e = σ.1}) =
              ∑ c ∈ U, ∑ σ ∈ S, edgePairCount left right c σ
          rw [Finset.sum_attach U
            (fun c : C =>
              ∑ σ ∈ S.attach,
                Fintype.card {e : E // left e = c ∧ right e = σ.1})]
          apply Finset.sum_congr rfl
          intro c _hc
          rw [Finset.sum_attach S
            (fun σ : Fin T =>
              Fintype.card {e : E // left e = c ∧ right e = σ})]
          apply Finset.sum_congr rfl
          intro σ _hσ
          rw [edgePairCount]
          rw [← Fintype.card_subtype
            (fun e : E => left e = c ∧ right e = σ)]

theorem rawZeroOneMatrix_one
    {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Finite C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E]
    (left : E → C) (right : E → Fin 1) (active : X → Finset C)
    (hActive : ∀ x : X, (active x).card = 1)
    (hLeft : ∀ c : C, edgeLeftDegree left c = activeDegree active c)
    (hRight : ∀ σ : Fin 1, edgeRightDegree right σ = Fintype.card X)
    (hRect : ∀ U : Finset C, ∀ S : Finset (Fin 1),
      edgeRectCount left right U S
        ≤ ∑ x : X, min ((active x ∩ U).card) S.card) :
    ∃ z : E → X → Nat,
      (∀ e x, z e x ≤ 1) ∧
      (∀ e, (∑ x : X, z e x) = 1) ∧
      (∀ e x, z e x = 1 → left e ∈ active x) ∧
      (∀ x σ, (∑ e : E, if right e = σ then z e x else 0) = 1) ∧
      (∀ x c, c ∈ active x →
        (∑ e : E, if left e = c then z e x else 0) = 1) := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  let I : Incidence 1 X C := {
    active := active
    active_card := hActive
  }
  let m : C → Fin 1 → Nat := fun c σ => edgePairCount left right c σ
  have hrow : ∀ c : C, (∑ σ : Fin 1, m c σ) = I.colorDegree c := by
    intro c
    rw [← edgeLeftDegree_eq_sum_edgePairCount left right c]
    simpa [I, Incidence.colorDegree, activeDegree] using hLeft c
  have hcol : ∀ σ : Fin 1, (∑ c : C, m c σ) = Fintype.card X := by
    intro σ
    rw [← edgeRightDegree_eq_sum_edgePairCount left right σ]
    exact hRight σ
  let M : CountMatrix I := {
    val := m
    row_sum := hrow
    col_sum := hcol
  }
  have hHall : M.HallCuts := by
    intro U S
    change (∑ c ∈ U, ∑ σ ∈ S, m c σ) ≤ I.cutCap U S
    rw [← edgeRectCount_eq_sum_edgePairCount left right U S]
    simpa [I, Incidence.cutCap] using hRect U S
  rcases hallRealization_one I M hHall with ⟨Φ, hΦ⟩
  have hη :
      ∀ c : C, ∀ σ : Fin 1,
        Incidence.choiceDegree (fun x : X => ((Φ.equiv x) σ).1) c =
          edgePairCount left right c σ := by
    intro c σ
    change Incidence.choiceDegree (fun x : X => Φ.color x σ) c =
      edgePairCount left right c σ
    rw [← Φ.count_eq_choiceDegree c σ]
    simpa [M, m] using hΦ c σ
  rcases rawExactEdgeColoring_of_exactWitness left right active Φ.equiv hη with
    ⟨κ, hκActive, hκRight, hκLeft⟩
  exact rawZeroOneMatrix_of_rawExactWitness
    left right active κ hκActive hκRight hκLeft

theorem rawZeroOneMatrix_two
    {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Finite C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E]
    (left : E → C) (right : E → Fin 2) (active : X → Finset C)
    (hActive : ∀ x : X, (active x).card = 2)
    (hLeft : ∀ c : C, edgeLeftDegree left c = activeDegree active c)
    (hRight : ∀ σ : Fin 2, edgeRightDegree right σ = Fintype.card X)
    (hRect : ∀ U : Finset C, ∀ S : Finset (Fin 2),
      edgeRectCount left right U S
        ≤ ∑ x : X, min ((active x ∩ U).card) S.card) :
    ∃ z : E → X → Nat,
      (∀ e x, z e x ≤ 1) ∧
      (∀ e, (∑ x : X, z e x) = 1) ∧
      (∀ e x, z e x = 1 → left e ∈ active x) ∧
      (∀ x σ, (∑ e : E, if right e = σ then z e x else 0) = 1) ∧
      (∀ x c, c ∈ active x →
        (∑ e : E, if left e = c then z e x else 0) = 1) := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  let I : Incidence 2 X C := {
    active := active
    active_card := hActive
  }
  let m : C → Fin 2 → Nat := fun c σ => edgePairCount left right c σ
  have hrow : ∀ c : C, (∑ σ : Fin 2, m c σ) = I.colorDegree c := by
    intro c
    rw [← edgeLeftDegree_eq_sum_edgePairCount left right c]
    simpa [I, Incidence.colorDegree, activeDegree] using hLeft c
  have hcol : ∀ σ : Fin 2, (∑ c : C, m c σ) = Fintype.card X := by
    intro σ
    rw [← edgeRightDegree_eq_sum_edgePairCount left right σ]
    exact hRight σ
  let M : CountMatrix I := {
    val := m
    row_sum := hrow
    col_sum := hcol
  }
  have hHall : M.HallCuts := by
    intro U S
    change (∑ c ∈ U, ∑ σ ∈ S, m c σ) ≤ I.cutCap U S
    rw [← edgeRectCount_eq_sum_edgePairCount left right U S]
    simpa [I, Incidence.cutCap] using hRect U S
  rcases hallRealization_two I M hHall with ⟨Φ, hΦ⟩
  have hη :
      ∀ c : C, ∀ σ : Fin 2,
        Incidence.choiceDegree (fun x : X => ((Φ.equiv x) σ).1) c =
          edgePairCount left right c σ := by
    intro c σ
    change Incidence.choiceDegree (fun x : X => Φ.color x σ) c =
      edgePairCount left right c σ
    rw [← Φ.count_eq_choiceDegree c σ]
    simpa [M, m] using hΦ c σ
  rcases rawExactEdgeColoring_of_exactWitness left right active Φ.equiv hη with
    ⟨κ, hκActive, hκRight, hκLeft⟩
  exact rawZeroOneMatrix_of_rawExactWitness
    left right active κ hκActive hκRight hκLeft

theorem rawZeroOneMatrix_of_T_le_two
    {T : Nat} (hT : T ≤ 2)
    {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Finite C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E]
    (left : E → C) (right : E → Fin T) (active : X → Finset C)
    (hActive : ∀ x : X, (active x).card = T)
    (hLeft : ∀ c : C, edgeLeftDegree left c = activeDegree active c)
    (hRight : ∀ σ : Fin T, edgeRightDegree right σ = Fintype.card X)
    (hRect : ∀ U : Finset C, ∀ S : Finset (Fin T),
      edgeRectCount left right U S
        ≤ ∑ x : X, min ((active x ∩ U).card) S.card) :
    ∃ z : E → X → Nat,
      (∀ e x, z e x ≤ 1) ∧
      (∀ e, (∑ x : X, z e x) = 1) ∧
      (∀ e x, z e x = 1 → left e ∈ active x) ∧
      (∀ x σ, (∑ e : E, if right e = σ then z e x else 0) = 1) ∧
      (∀ x c, c ∈ active x →
        (∑ e : E, if left e = c then z e x else 0) = 1) := by
  classical
  interval_cases T
  · exact rawZeroOneMatrix_zero left right active hActive hLeft hRight hRect
  · exact rawZeroOneMatrix_one left right active hActive hLeft hRight hRect
  · exact rawZeroOneMatrix_two left right active hActive hLeft hRight hRect

theorem rawZeroOneMatrix_three_of_singletonSelection
    (hSelect : EraseLastHallCutsTwoSingletonSelectionGoal.{uX, uC})
    {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Finite C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E]
    (left : E → C) (right : E → Fin 3) (active : X → Finset C)
    (hActive : ∀ x : X, (active x).card = 3)
    (hLeft : ∀ c : C, edgeLeftDegree left c = activeDegree active c)
    (hRight : ∀ σ : Fin 3, edgeRightDegree right σ = Fintype.card X)
    (hRect : ∀ U : Finset C, ∀ S : Finset (Fin 3),
      edgeRectCount left right U S
        ≤ ∑ x : X, min ((active x ∩ U).card) S.card) :
    ∃ z : E → X → Nat,
      (∀ e x, z e x ≤ 1) ∧
      (∀ e, (∑ x : X, z e x) = 1) ∧
      (∀ e x, z e x = 1 → left e ∈ active x) ∧
      (∀ x σ, (∑ e : E, if right e = σ then z e x else 0) = 1) ∧
      (∀ x c, c ∈ active x →
        (∑ e : E, if left e = c then z e x else 0) = 1) := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  let I : Incidence 3 X C := {
    active := active
    active_card := hActive
  }
  let m : C → Fin 3 → Nat := fun c σ => edgePairCount left right c σ
  have hrow : ∀ c : C, (∑ σ : Fin 3, m c σ) = I.colorDegree c := by
    intro c
    rw [← edgeLeftDegree_eq_sum_edgePairCount left right c]
    simpa [I, Incidence.colorDegree, activeDegree] using hLeft c
  have hcol : ∀ σ : Fin 3, (∑ c : C, m c σ) = Fintype.card X := by
    intro σ
    rw [← edgeRightDegree_eq_sum_edgePairCount left right σ]
    exact hRight σ
  let M : CountMatrix I := {
    val := m
    row_sum := hrow
    col_sum := hcol
  }
  have hHall : M.HallCuts := by
    intro U S
    change (∑ c ∈ U, ∑ σ ∈ S, m c σ) ≤ I.cutCap U S
    rw [← edgeRectCount_eq_sum_edgePairCount left right U S]
    simpa [I, Incidence.cutCap] using hRect U S
  rcases hallRealization_three_of_singletonSelection hSelect I M hHall with
    ⟨Φ, hΦ⟩
  have hη :
      ∀ c : C, ∀ σ : Fin 3,
        Incidence.choiceDegree (fun x : X => ((Φ.equiv x) σ).1) c =
          edgePairCount left right c σ := by
    intro c σ
    change Incidence.choiceDegree (fun x : X => Φ.color x σ) c =
      edgePairCount left right c σ
    rw [← Φ.count_eq_choiceDegree c σ]
    simpa [M, m] using hΦ c σ
  rcases rawExactEdgeColoring_of_exactWitness left right active Φ.equiv hη with
    ⟨κ, hκActive, hκRight, hκLeft⟩
  exact rawZeroOneMatrix_of_rawExactWitness
    left right active κ hκActive hκRight hκLeft

theorem rawZeroOneMatrix_three_of_singletonCutSlackSelection
    (hSelect : EraseLastHallCutsTwoSingletonCutSlackSelectionGoal.{uX, uC})
    {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Finite C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E]
    (left : E → C) (right : E → Fin 3) (active : X → Finset C)
    (hActive : ∀ x : X, (active x).card = 3)
    (hLeft : ∀ c : C, edgeLeftDegree left c = activeDegree active c)
    (hRight : ∀ σ : Fin 3, edgeRightDegree right σ = Fintype.card X)
    (hRect : ∀ U : Finset C, ∀ S : Finset (Fin 3),
      edgeRectCount left right U S
        ≤ ∑ x : X, min ((active x ∩ U).card) S.card) :
    ∃ z : E → X → Nat,
      (∀ e x, z e x ≤ 1) ∧
      (∀ e, (∑ x : X, z e x) = 1) ∧
      (∀ e x, z e x = 1 → left e ∈ active x) ∧
      (∀ x σ, (∑ e : E, if right e = σ then z e x else 0) = 1) ∧
      (∀ x c, c ∈ active x →
        (∑ e : E, if left e = c then z e x else 0) = 1) :=
  rawZeroOneMatrix_three_of_singletonSelection
    (eraseLastHallCutsTwoSingletonSelectionGoal_of_cutSlack hSelect)
    left right active hActive hLeft hRight hRect

theorem rawZeroOneMatrix_three_of_singletonTokenCutSlackSelection
    (hToken : EraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal.{uX, uC})
    {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Finite C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E]
    (left : E → C) (right : E → Fin 3) (active : X → Finset C)
    (hActive : ∀ x : X, (active x).card = 3)
    (hLeft : ∀ c : C, edgeLeftDegree left c = activeDegree active c)
    (hRight : ∀ σ : Fin 3, edgeRightDegree right σ = Fintype.card X)
    (hRect : ∀ U : Finset C, ∀ S : Finset (Fin 3),
      edgeRectCount left right U S
        ≤ ∑ x : X, min ((active x ∩ U).card) S.card) :
    ∃ z : E → X → Nat,
      (∀ e x, z e x ≤ 1) ∧
      (∀ e, (∑ x : X, z e x) = 1) ∧
      (∀ e x, z e x = 1 → left e ∈ active x) ∧
      (∀ x σ, (∑ e : E, if right e = σ then z e x else 0) = 1) ∧
      (∀ x c, c ∈ active x →
        (∑ e : E, if left e = c then z e x else 0) = 1) :=
  rawZeroOneMatrix_three_of_singletonCutSlackSelection
    (eraseLastHallCutsTwoSingletonCutSlackSelectionGoal_of_token hToken)
    left right active hActive hLeft hRight hRect

theorem rawZeroOneMatrix_three_of_singletonProperTokenCutSlackSelection
    (hProper :
      EraseLastHallCutsTwoSingletonProperTokenCutSlackSelectionGoal.{uX, uC})
    {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Finite C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E]
    (left : E → C) (right : E → Fin 3) (active : X → Finset C)
    (hActive : ∀ x : X, (active x).card = 3)
    (hLeft : ∀ c : C, edgeLeftDegree left c = activeDegree active c)
    (hRight : ∀ σ : Fin 3, edgeRightDegree right σ = Fintype.card X)
    (hRect : ∀ U : Finset C, ∀ S : Finset (Fin 3),
      edgeRectCount left right U S
        ≤ ∑ x : X, min ((active x ∩ U).card) S.card) :
    ∃ z : E → X → Nat,
      (∀ e x, z e x ≤ 1) ∧
      (∀ e, (∑ x : X, z e x) = 1) ∧
      (∀ e x, z e x = 1 → left e ∈ active x) ∧
      (∀ x σ, (∑ e : E, if right e = σ then z e x else 0) = 1) ∧
      (∀ x c, c ∈ active x →
        (∑ e : E, if left e = c then z e x else 0) = 1) :=
  rawZeroOneMatrix_three_of_singletonTokenCutSlackSelection
    (eraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal_of_proper
      hProper)
    left right active hActive hLeft hRight hRect

theorem rawZeroOneMatrix_three_of_singletonProperTokenQuotaSelection
    (hQuota :
      EraseLastHallCutsTwoSingletonProperTokenQuotaSelectionGoal.{uX, uC})
    {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Finite C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E]
    (left : E → C) (right : E → Fin 3) (active : X → Finset C)
    (hActive : ∀ x : X, (active x).card = 3)
    (hLeft : ∀ c : C, edgeLeftDegree left c = activeDegree active c)
    (hRight : ∀ σ : Fin 3, edgeRightDegree right σ = Fintype.card X)
    (hRect : ∀ U : Finset C, ∀ S : Finset (Fin 3),
      edgeRectCount left right U S
        ≤ ∑ x : X, min ((active x ∩ U).card) S.card) :
    ∃ z : E → X → Nat,
      (∀ e x, z e x ≤ 1) ∧
      (∀ e, (∑ x : X, z e x) = 1) ∧
      (∀ e x, z e x = 1 → left e ∈ active x) ∧
      (∀ x σ, (∑ e : E, if right e = σ then z e x else 0) = 1) ∧
      (∀ x c, c ∈ active x →
        (∑ e : E, if left e = c then z e x else 0) = 1) :=
  rawZeroOneMatrix_three_of_singletonProperTokenCutSlackSelection
    (eraseLastHallCutsTwoSingletonProperTokenCutSlackSelectionGoal_of_quota
      hQuota)
    left right active hActive hLeft hRight hRect

theorem rawZeroOneMatrix_four_of_eraseLastHallCutsFourGoal
    (hFour : EraseLastHallCutsFourGoal.{uX, uC})
    (hToken : EraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal.{uX, uC})
    {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Finite C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E]
    (left : E → C) (right : E → Fin 4) (active : X → Finset C)
    (hActive : ∀ x : X, (active x).card = 4)
    (hLeft : ∀ c : C, edgeLeftDegree left c = activeDegree active c)
    (hRight : ∀ σ : Fin 4, edgeRightDegree right σ = Fintype.card X)
    (hRect : ∀ U : Finset C, ∀ S : Finset (Fin 4),
      edgeRectCount left right U S
        ≤ ∑ x : X, min ((active x ∩ U).card) S.card) :
    ∃ z : E → X → Nat,
      (∀ e x, z e x ≤ 1) ∧
      (∀ e, (∑ x : X, z e x) = 1) ∧
      (∀ e x, z e x = 1 → left e ∈ active x) ∧
      (∀ x σ, (∑ e : E, if right e = σ then z e x else 0) = 1) ∧
      (∀ x c, c ∈ active x →
        (∑ e : E, if left e = c then z e x else 0) = 1) := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  let I : Incidence 4 X C := {
    active := active
    active_card := hActive
  }
  let m : C → Fin 4 → Nat := fun c σ => edgePairCount left right c σ
  have hrow : ∀ c : C, (∑ σ : Fin 4, m c σ) = I.colorDegree c := by
    intro c
    rw [← edgeLeftDegree_eq_sum_edgePairCount left right c]
    simpa [I, Incidence.colorDegree, activeDegree] using hLeft c
  have hcol : ∀ σ : Fin 4, (∑ c : C, m c σ) = Fintype.card X := by
    intro σ
    rw [← edgeRightDegree_eq_sum_edgePairCount left right σ]
    exact hRight σ
  let M : CountMatrix I := {
    val := m
    row_sum := hrow
    col_sum := hcol
  }
  have hHall : M.HallCuts := by
    intro U S
    change (∑ c ∈ U, ∑ σ ∈ S, m c σ) ≤ I.cutCap U S
    rw [← edgeRectCount_eq_sum_edgePairCount left right U S]
    simpa [I, Incidence.cutCap] using hRect U S
  rcases
      hallRealization_four_of_eraseLastHallCutsFourGoal
        hFour hToken I M hHall with
    ⟨Φ, hΦ⟩
  have hη :
      ∀ c : C, ∀ σ : Fin 4,
        Incidence.choiceDegree (fun x : X => ((Φ.equiv x) σ).1) c =
          edgePairCount left right c σ := by
    intro c σ
    change Incidence.choiceDegree (fun x : X => Φ.color x σ) c =
      edgePairCount left right c σ
    rw [← Φ.count_eq_choiceDegree c σ]
    simpa [M, m] using hΦ c σ
  rcases rawExactEdgeColoring_of_exactWitness left right active Φ.equiv hη with
    ⟨κ, hκActive, hκRight, hκLeft⟩
  exact rawZeroOneMatrix_of_rawExactWitness
    left right active κ hκActive hκRight hκLeft

theorem rawZeroOneMatrix_four_of_fourTokenCutSlackSelection
    (hFourToken :
      EraseLastHallCutsFourTokenCutSlackSelectionGoal.{uX, uC})
    (hToken : EraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal.{uX, uC}) :
    ∀ {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Finite C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E],
    ∀ (left : E → C) (right : E → Fin 4) (active : X → Finset C),
    (∀ x : X, (active x).card = 4) →
    (∀ c : C, edgeLeftDegree left c = activeDegree active c) →
    (∀ σ : Fin 4, edgeRightDegree right σ = Fintype.card X) →
    (∀ U : Finset C, ∀ S : Finset (Fin 4),
      edgeRectCount left right U S
        ≤ ∑ x : X, min ((active x ∩ U).card) S.card) →
    ∃ z : E → X → Nat,
      (∀ e x, z e x ≤ 1) ∧
      (∀ e, (∑ x : X, z e x) = 1) ∧
      (∀ e x, z e x = 1 → left e ∈ active x) ∧
      (∀ x σ, (∑ e : E, if right e = σ then z e x else 0) = 1) ∧
      (∀ x c, c ∈ active x →
        (∑ e : E, if left e = c then z e x else 0) = 1) :=
  rawZeroOneMatrix_four_of_eraseLastHallCutsFourGoal
    (eraseLastHallCutsFourGoal_of_tokenCutSlackSelection hFourToken)
    hToken

theorem rawZeroOneMatrix_four_of_fourSmallTokenCutSlackSelection
    (hFourSmall :
      EraseLastHallCutsFourSmallTokenCutSlackSelectionGoal.{uX, uC})
    (hToken : EraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal.{uX, uC}) :
    ∀ {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Finite C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E],
    ∀ (left : E → C) (right : E → Fin 4) (active : X → Finset C),
    (∀ x : X, (active x).card = 4) →
    (∀ c : C, edgeLeftDegree left c = activeDegree active c) →
    (∀ σ : Fin 4, edgeRightDegree right σ = Fintype.card X) →
    (∀ U : Finset C, ∀ S : Finset (Fin 4),
      edgeRectCount left right U S
        ≤ ∑ x : X, min ((active x ∩ U).card) S.card) →
    ∃ z : E → X → Nat,
      (∀ e x, z e x ≤ 1) ∧
      (∀ e, (∑ x : X, z e x) = 1) ∧
      (∀ e x, z e x = 1 → left e ∈ active x) ∧
      (∀ x σ, (∑ e : E, if right e = σ then z e x else 0) = 1) ∧
      (∀ x c, c ∈ active x →
        (∑ e : E, if left e = c then z e x else 0) = 1) :=
  rawZeroOneMatrix_four_of_fourTokenCutSlackSelection
    (eraseLastHallCutsFourTokenCutSlackSelectionGoal_of_small hFourSmall)
    hToken

theorem rawZeroOneMatrix_four_of_fourSingletonPairTokenCutSlackSelection
    (hFourSP :
      EraseLastHallCutsFourSingletonPairTokenCutSlackSelectionGoal.{uX, uC})
    (hToken : EraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal.{uX, uC}) :
    ∀ {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Finite C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E],
    ∀ (left : E → C) (right : E → Fin 4) (active : X → Finset C),
    (∀ x : X, (active x).card = 4) →
    (∀ c : C, edgeLeftDegree left c = activeDegree active c) →
    (∀ σ : Fin 4, edgeRightDegree right σ = Fintype.card X) →
    (∀ U : Finset C, ∀ S : Finset (Fin 4),
      edgeRectCount left right U S
        ≤ ∑ x : X, min ((active x ∩ U).card) S.card) →
    ∃ z : E → X → Nat,
      (∀ e x, z e x ≤ 1) ∧
      (∀ e, (∑ x : X, z e x) = 1) ∧
      (∀ e x, z e x = 1 → left e ∈ active x) ∧
      (∀ x σ, (∑ e : E, if right e = σ then z e x else 0) = 1) ∧
      (∀ x c, c ∈ active x →
        (∑ e : E, if left e = c then z e x else 0) = 1) :=
  rawZeroOneMatrix_four_of_fourSmallTokenCutSlackSelection
    (eraseLastHallCutsFourSmallTokenCutSlackSelectionGoal_of_singletonPair
      hFourSP)
    hToken

theorem rawZeroOneMatrix_four_of_fourSingletonPairTokenQuotaSelection
    (hFourQuota :
      EraseLastHallCutsFourSingletonPairTokenQuotaSelectionGoal.{uX, uC})
    (hToken : EraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal.{uX, uC}) :
    ∀ {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Finite C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E],
    ∀ (left : E → C) (right : E → Fin 4) (active : X → Finset C),
    (∀ x : X, (active x).card = 4) →
    (∀ c : C, edgeLeftDegree left c = activeDegree active c) →
    (∀ σ : Fin 4, edgeRightDegree right σ = Fintype.card X) →
    (∀ U : Finset C, ∀ S : Finset (Fin 4),
      edgeRectCount left right U S
        ≤ ∑ x : X, min ((active x ∩ U).card) S.card) →
    ∃ z : E → X → Nat,
      (∀ e x, z e x ≤ 1) ∧
      (∀ e, (∑ x : X, z e x) = 1) ∧
      (∀ e x, z e x = 1 → left e ∈ active x) ∧
      (∀ x σ, (∑ e : E, if right e = σ then z e x else 0) = 1) ∧
      (∀ x c, c ∈ active x →
        (∑ e : E, if left e = c then z e x else 0) = 1) :=
  rawZeroOneMatrix_four_of_fourSingletonPairTokenCutSlackSelection
    (eraseLastHallCutsFourSingletonPairTokenCutSlackSelectionGoal_of_quota
      hFourQuota)
    hToken

theorem rawZeroOneMatrix_of_T_le_three_of_singletonSelection
    (hSelect : EraseLastHallCutsTwoSingletonSelectionGoal.{uX, uC})
    {T : Nat} (hT : T ≤ 3)
    {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Finite C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E]
    (left : E → C) (right : E → Fin T) (active : X → Finset C)
    (hActive : ∀ x : X, (active x).card = T)
    (hLeft : ∀ c : C, edgeLeftDegree left c = activeDegree active c)
    (hRight : ∀ σ : Fin T, edgeRightDegree right σ = Fintype.card X)
    (hRect : ∀ U : Finset C, ∀ S : Finset (Fin T),
      edgeRectCount left right U S
        ≤ ∑ x : X, min ((active x ∩ U).card) S.card) :
    ∃ z : E → X → Nat,
      (∀ e x, z e x ≤ 1) ∧
      (∀ e, (∑ x : X, z e x) = 1) ∧
      (∀ e x, z e x = 1 → left e ∈ active x) ∧
      (∀ x σ, (∑ e : E, if right e = σ then z e x else 0) = 1) ∧
      (∀ x c, c ∈ active x →
        (∑ e : E, if left e = c then z e x else 0) = 1) := by
  classical
  interval_cases T
  · exact rawZeroOneMatrix_zero left right active hActive hLeft hRight hRect
  · exact rawZeroOneMatrix_one left right active hActive hLeft hRight hRect
  · exact rawZeroOneMatrix_two left right active hActive hLeft hRight hRect
  · exact rawZeroOneMatrix_three_of_singletonSelection hSelect
      left right active hActive hLeft hRight hRect

theorem rawZeroOneMatrix_of_T_le_three_of_singletonCutSlackSelection
    (hSelect : EraseLastHallCutsTwoSingletonCutSlackSelectionGoal.{uX, uC})
    {T : Nat} (hT : T ≤ 3)
    {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Finite C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E]
    (left : E → C) (right : E → Fin T) (active : X → Finset C)
    (hActive : ∀ x : X, (active x).card = T)
    (hLeft : ∀ c : C, edgeLeftDegree left c = activeDegree active c)
    (hRight : ∀ σ : Fin T, edgeRightDegree right σ = Fintype.card X)
    (hRect : ∀ U : Finset C, ∀ S : Finset (Fin T),
      edgeRectCount left right U S
        ≤ ∑ x : X, min ((active x ∩ U).card) S.card) :
    ∃ z : E → X → Nat,
      (∀ e x, z e x ≤ 1) ∧
      (∀ e, (∑ x : X, z e x) = 1) ∧
      (∀ e x, z e x = 1 → left e ∈ active x) ∧
      (∀ x σ, (∑ e : E, if right e = σ then z e x else 0) = 1) ∧
      (∀ x c, c ∈ active x →
        (∑ e : E, if left e = c then z e x else 0) = 1) :=
  rawZeroOneMatrix_of_T_le_three_of_singletonSelection
    (eraseLastHallCutsTwoSingletonSelectionGoal_of_cutSlack hSelect)
    hT left right active hActive hLeft hRight hRect

theorem rawZeroOneMatrix_of_T_le_three_of_singletonTokenCutSlackSelection
    (hToken : EraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal.{uX, uC})
    {T : Nat} (hT : T ≤ 3)
    {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Finite C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E]
    (left : E → C) (right : E → Fin T) (active : X → Finset C)
    (hActive : ∀ x : X, (active x).card = T)
    (hLeft : ∀ c : C, edgeLeftDegree left c = activeDegree active c)
    (hRight : ∀ σ : Fin T, edgeRightDegree right σ = Fintype.card X)
    (hRect : ∀ U : Finset C, ∀ S : Finset (Fin T),
      edgeRectCount left right U S
        ≤ ∑ x : X, min ((active x ∩ U).card) S.card) :
    ∃ z : E → X → Nat,
      (∀ e x, z e x ≤ 1) ∧
      (∀ e, (∑ x : X, z e x) = 1) ∧
      (∀ e x, z e x = 1 → left e ∈ active x) ∧
      (∀ x σ, (∑ e : E, if right e = σ then z e x else 0) = 1) ∧
      (∀ x c, c ∈ active x →
        (∑ e : E, if left e = c then z e x else 0) = 1) :=
  rawZeroOneMatrix_of_T_le_three_of_singletonCutSlackSelection
    (eraseLastHallCutsTwoSingletonCutSlackSelectionGoal_of_token hToken)
    hT left right active hActive hLeft hRight hRect

theorem rawZeroOneMatrix_of_T_le_three_of_singletonProperTokenCutSlackSelection
    (hProper :
      EraseLastHallCutsTwoSingletonProperTokenCutSlackSelectionGoal.{uX, uC})
    {T : Nat} (hT : T ≤ 3)
    {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Finite C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E]
    (left : E → C) (right : E → Fin T) (active : X → Finset C)
    (hActive : ∀ x : X, (active x).card = T)
    (hLeft : ∀ c : C, edgeLeftDegree left c = activeDegree active c)
    (hRight : ∀ σ : Fin T, edgeRightDegree right σ = Fintype.card X)
    (hRect : ∀ U : Finset C, ∀ S : Finset (Fin T),
      edgeRectCount left right U S
        ≤ ∑ x : X, min ((active x ∩ U).card) S.card) :
    ∃ z : E → X → Nat,
      (∀ e x, z e x ≤ 1) ∧
      (∀ e, (∑ x : X, z e x) = 1) ∧
      (∀ e x, z e x = 1 → left e ∈ active x) ∧
      (∀ x σ, (∑ e : E, if right e = σ then z e x else 0) = 1) ∧
      (∀ x c, c ∈ active x →
        (∑ e : E, if left e = c then z e x else 0) = 1) :=
  rawZeroOneMatrix_of_T_le_three_of_singletonTokenCutSlackSelection
    (eraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal_of_proper
      hProper)
    hT left right active hActive hLeft hRight hRect

theorem rawZeroOneMatrix_of_T_le_three_of_singletonProperTokenQuotaSelection
    (hQuota :
      EraseLastHallCutsTwoSingletonProperTokenQuotaSelectionGoal.{uX, uC})
    {T : Nat} (hT : T ≤ 3)
    {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Finite C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E]
    (left : E → C) (right : E → Fin T) (active : X → Finset C)
    (hActive : ∀ x : X, (active x).card = T)
    (hLeft : ∀ c : C, edgeLeftDegree left c = activeDegree active c)
    (hRight : ∀ σ : Fin T, edgeRightDegree right σ = Fintype.card X)
    (hRect : ∀ U : Finset C, ∀ S : Finset (Fin T),
      edgeRectCount left right U S
        ≤ ∑ x : X, min ((active x ∩ U).card) S.card) :
    ∃ z : E → X → Nat,
      (∀ e x, z e x ≤ 1) ∧
      (∀ e, (∑ x : X, z e x) = 1) ∧
      (∀ e x, z e x = 1 → left e ∈ active x) ∧
      (∀ x σ, (∑ e : E, if right e = σ then z e x else 0) = 1) ∧
      (∀ x c, c ∈ active x →
        (∑ e : E, if left e = c then z e x else 0) = 1) :=
  rawZeroOneMatrix_of_T_le_three_of_singletonProperTokenCutSlackSelection
    (eraseLastHallCutsTwoSingletonProperTokenCutSlackSelectionGoal_of_quota
      hQuota)
    hT left right active hActive hLeft hRight hRect

theorem exactEdgeColoringGoal_of_hoffmanOrderedSDRGoal
    (hHoffman : HoffmanOrderedSDRGoal.{uX, uC}) :
    ExactEdgeColoringGoal.{uX, uC} := by
  classical
  intro T X C E _instX _instC _instE _decX _decC _decE
    left right active hActive hLeft hRight hRect
  let I : Incidence T X C := {
    active := active
    active_card := hActive
  }
  let m : C → Fin T → Nat := fun c σ => edgePairCount left right c σ
  have hrow : ∀ c : C, (∑ σ : Fin T, m c σ) = I.colorDegree c := by
    intro c
    rw [← edgeLeftDegree_eq_sum_edgePairCount left right c]
    simpa [I, Incidence.colorDegree, activeDegree] using hLeft c
  have hcol : ∀ σ : Fin T, (∑ c : C, m c σ) = Fintype.card X := by
    intro σ
    rw [← edgeRightDegree_eq_sum_edgePairCount left right σ]
    exact hRight σ
  have hcut :
      ∀ U : Finset C, ∀ S : Finset (Fin T),
        (∑ c ∈ U, ∑ σ ∈ S, m c σ) ≤ I.cutCap U S := by
    intro U S
    rw [← edgeRectCount_eq_sum_edgePairCount left right U S]
    simpa [I, Incidence.cutCap] using hRect U S
  rcases hHoffman I m hrow hcol hcut with ⟨η, hη⟩
  refine ⟨η, ?_⟩
  intro c σ
  exact hη c σ

theorem exactEdgeColoringGoal_iff_hoffmanOrderedSDRGoal :
    ExactEdgeColoringGoal.{uX, uC} ↔ HoffmanOrderedSDRGoal.{uX, uC} :=
  ⟨hoffmanOrderedSDRGoal_of_exactEdgeColoring,
    exactEdgeColoringGoal_of_hoffmanOrderedSDRGoal⟩

theorem exactEdgeColoringGoal_of_hallRealizationGoal
    (hHall : HallRealizationGoal.{uX, uC}) :
    ExactEdgeColoringGoal.{uX, uC} :=
  exactEdgeColoringGoal_of_hoffmanOrderedSDRGoal
    (hoffmanOrderedSDRGoal_of_hallRealization hHall)

theorem exactEdgeColoringGoal_iff_hallRealizationGoal :
    ExactEdgeColoringGoal.{uX, uC} ↔ HallRealizationGoal.{uX, uC} :=
  ⟨hallRealizationGoal_of_exactEdgeColoring,
    exactEdgeColoringGoal_of_hallRealizationGoal⟩

theorem rawExactEdgeColoringGoal_of_hallRealizationGoal
    (hHall : HallRealizationGoal.{uX, uC}) :
    RawExactEdgeColoringGoal.{uX, uC} :=
  rawExactEdgeColoringGoal_of_exactEdgeColoringGoal
    (exactEdgeColoringGoal_of_hallRealizationGoal hHall)

theorem rawZeroOneMatrixGoal_of_hallRealizationGoal
    (hHall : HallRealizationGoal.{uX, uC}) :
    RawZeroOneMatrixGoal.{uX, uC} :=
  rawZeroOneMatrixGoal_of_rawExactEdgeColoringGoal
    (rawExactEdgeColoringGoal_of_hallRealizationGoal hHall)

theorem rawZeroOneMatrixGoal_iff_hallRealizationGoal :
    RawZeroOneMatrixGoal.{uX, uC} ↔ HallRealizationGoal.{uX, uC} :=
  ⟨fun hRaw => hallRealizationGoal_of_exactEdgeColoring
      (exactEdgeColoringGoal_of_raw
        (rawExactEdgeColoringGoal_of_rawMatrix hRaw)),
    rawZeroOneMatrixGoal_of_hallRealizationGoal⟩

theorem hallRealizationGoal_of_compatibleDeWerraGoal
    (hDW : CompatibleDeWerraGoal.{uX, uC}) :
    HallRealizationGoal.{uX, uC} :=
  hallRealizationGoal_of_exactEdgeColoring
    (exactEdgeColoringGoal_of_compatibleDeWerra hDW)

theorem hallRealizationGoal_of_compatibleZeroOneMatrixGoal
    (hMat : CompatibleZeroOneMatrixGoal.{uX, uC}) :
    HallRealizationGoal.{uX, uC} :=
  hallRealizationGoal_of_compatibleDeWerraGoal
    (compatibleDeWerraGoal_of_matrix hMat)

theorem hallRealizationGoal_of_rawZeroOneMatrixGoal
    (hRaw : RawZeroOneMatrixGoal.{uX, uC}) :
    HallRealizationGoal.{uX, uC} :=
  (rawZeroOneMatrixGoal_iff_hallRealizationGoal).1 hRaw

/--
A finite obstruction to the unrestricted one-sided raw/Hall realization
endpoint.

The active sets have `T = 3`, `X = Fin 5`, and `C = Fin 6`.  The count matrix
has the required row sums, column sums, and Hall rectangle cuts, but any local
symboling realizing its zero pattern forces vertices `0`, `1`, and `4` to place
colour `1` in symbol `1`, while the matrix contains only two copies of that
cell.
-/
theorem not_hallRealizationGoal :
    ¬ HallRealizationGoal.{0, 0} := by
  classical
  intro hHall
  let active : Fin 5 → Finset (Fin 6) := fun x =>
    if x = 0 then ({1, 0, 2} : Finset (Fin 6)) else
    if x = 1 then ({1, 3, 4} : Finset (Fin 6)) else
    if x = 2 then ({2, 3, 5} : Finset (Fin 6)) else
    if x = 3 then ({2, 4, 5} : Finset (Fin 6)) else
      ({1, 0, 4} : Finset (Fin 6))
  have hActive : ∀ x : Fin 5, (active x).card = 3 := by
    decide
  let I : Incidence 3 (Fin 5) (Fin 6) := {
    active := active
    active_card := hActive
  }
  let mVal : Fin 6 → Fin 3 → Nat := fun c σ =>
    if c = 0 then
      if σ = 0 then 0 else if σ = 1 then 0 else 2
    else if c = 1 then
      if σ = 0 then 0 else if σ = 1 then 2 else 1
    else if c = 2 then
      if σ = 0 then 1 else if σ = 1 then 1 else 1
    else if c = 3 then
      if σ = 0 then 1 else if σ = 1 then 0 else 1
    else if c = 4 then
      if σ = 0 then 3 else if σ = 1 then 0 else 0
    else
      if σ = 0 then 0 else if σ = 1 then 2 else 0
  have hrow : ∀ c : Fin 6, (∑ σ : Fin 3, mVal c σ) = I.colorDegree c := by
    intro c
    change (∑ σ : Fin 3, mVal c σ) =
      ((Finset.univ : Finset (Fin 5)).filter
        (fun x => c ∈ active x)).card
    decide +revert
  have hcol : ∀ σ : Fin 3, (∑ c : Fin 6, mVal c σ) = Fintype.card (Fin 5) := by
    decide
  let M : CountMatrix I := {
    val := mVal
    row_sum := hrow
    col_sum := hcol
  }
  have hCuts : M.HallCuts := by
    intro U S
    change (∑ c ∈ U, ∑ σ ∈ S, mVal c σ) ≤
      ∑ x : Fin 5, min ((active x ∩ U).card) S.card
    decide +revert
  rcases hHall I M hCuts with ⟨Φ, hReal⟩
  have color_pos :
      ∀ x : Fin 5, ∀ σ : Fin 3, 0 < mVal (Φ.color x σ) σ := by
    intro x σ
    have hmem :
        x ∈ (Finset.univ : Finset (Fin 5)).filter
            (fun y => Φ.color y σ = Φ.color x σ) := by
      simp
    have hchoicePos :
        0 <
          Incidence.choiceDegree
            (fun y : Fin 5 => Φ.color y σ) (Φ.color x σ) := by
      rw [Incidence.choiceDegree]
      exact Finset.card_pos.mpr ⟨x, hmem⟩
    have hcount :
        Incidence.choiceDegree
            (fun y : Fin 5 => Φ.color y σ) (Φ.color x σ) =
          mVal (Φ.color x σ) σ := by
      rw [← Φ.count_eq_choiceDegree (Φ.color x σ) σ]
      exact hReal (Φ.color x σ) σ
    omega
  have color_ne {x : Fin 5} {σ τ : Fin 3} (hστ : σ ≠ τ) :
      Φ.color x σ ≠ Φ.color x τ := by
    intro hcolor
    have hsub : Φ.equiv x σ = Φ.equiv x τ := Subtype.ext hcolor
    exact hστ ((Φ.equiv x).injective hsub)
  have hForce0 :
      ∀ a0 a1 a2 : Fin 6,
        a0 ∈ active 0 → a1 ∈ active 0 → a2 ∈ active 0 →
        0 < mVal a0 0 → 0 < mVal a1 1 → 0 < mVal a2 2 →
        a0 ≠ a1 → a0 ≠ a2 → a1 ≠ a2 → a1 = 1 := by
    decide
  have hForce1 :
      ∀ a0 a1 a2 : Fin 6,
        a0 ∈ active 1 → a1 ∈ active 1 → a2 ∈ active 1 →
        0 < mVal a0 0 → 0 < mVal a1 1 → 0 < mVal a2 2 →
        a0 ≠ a1 → a0 ≠ a2 → a1 ≠ a2 → a1 = 1 := by
    decide
  have hForce4 :
      ∀ a0 a1 a2 : Fin 6,
        a0 ∈ active 4 → a1 ∈ active 4 → a2 ∈ active 4 →
        0 < mVal a0 0 → 0 < mVal a1 1 → 0 < mVal a2 2 →
        a0 ≠ a1 → a0 ≠ a2 → a1 ≠ a2 → a1 = 1 := by
    decide
  have hΦ01 : Φ.color 0 (1 : Fin 3) = 1 :=
    hForce0 (Φ.color 0 0) (Φ.color 0 1) (Φ.color 0 2)
      (Φ.color_mem_active 0 0) (Φ.color_mem_active 0 1)
      (Φ.color_mem_active 0 2) (color_pos 0 0)
      (color_pos 0 1) (color_pos 0 2)
      (color_ne (by decide : (0 : Fin 3) ≠ 1))
      (color_ne (by decide : (0 : Fin 3) ≠ 2))
      (color_ne (by decide : (1 : Fin 3) ≠ 2))
  have hΦ11 : Φ.color 1 (1 : Fin 3) = 1 :=
    hForce1 (Φ.color 1 0) (Φ.color 1 1) (Φ.color 1 2)
      (Φ.color_mem_active 1 0) (Φ.color_mem_active 1 1)
      (Φ.color_mem_active 1 2) (color_pos 1 0)
      (color_pos 1 1) (color_pos 1 2)
      (color_ne (by decide : (0 : Fin 3) ≠ 1))
      (color_ne (by decide : (0 : Fin 3) ≠ 2))
      (color_ne (by decide : (1 : Fin 3) ≠ 2))
  have hΦ41 : Φ.color 4 (1 : Fin 3) = 1 :=
    hForce4 (Φ.color 4 0) (Φ.color 4 1) (Φ.color 4 2)
      (Φ.color_mem_active 4 0) (Φ.color_mem_active 4 1)
      (Φ.color_mem_active 4 2) (color_pos 4 0)
      (color_pos 4 1) (color_pos 4 2)
      (color_ne (by decide : (0 : Fin 3) ≠ 1))
      (color_ne (by decide : (0 : Fin 3) ≠ 2))
      (color_ne (by decide : (1 : Fin 3) ≠ 2))
  have hthree :
      3 ≤ Φ.count (1 : Fin 6) (1 : Fin 3) := by
    rw [Φ.count_eq_choiceDegree]
    unfold Incidence.choiceDegree
    let S : Finset (Fin 5) := {0, 1, 4}
    have hsub :
        S ⊆ (Finset.univ : Finset (Fin 5)).filter
          (fun x => Φ.color x (1 : Fin 3) = (1 : Fin 6)) := by
      intro x hx
      fin_cases x
      · simpa [S] using hΦ01
      · simpa [S] using hΦ11
      · simp [S] at hx
      · simp [S] at hx
      · simpa [S] using hΦ41
    have hScard : S.card = 3 := by
      decide
    have hcardle :
        S.card ≤
          ((Finset.univ : Finset (Fin 5)).filter
            (fun x => Φ.color x (1 : Fin 3) = (1 : Fin 6))).card :=
      Finset.card_le_card hsub
    have hcardle' :
        3 ≤
          ((Finset.univ : Finset (Fin 5)).filter
            (fun x => Φ.color x (1 : Fin 3) = (1 : Fin 6))).card := by
      omega
    change 3 ≤
      ((Finset.univ : Finset (Fin 5)).filter
        (fun x => Φ.color x (1 : Fin 3) = (1 : Fin 6))).card
    exact hcardle'
  have htwo : Φ.count (1 : Fin 6) (1 : Fin 3) = 2 := by
    simpa [M, mVal] using hReal (1 : Fin 6) (1 : Fin 3)
  omega

theorem not_rawZeroOneMatrixGoal :
    ¬ RawZeroOneMatrixGoal.{0, 0} := by
  intro hRaw
  exact not_hallRealizationGoal
    (hallRealizationGoal_of_rawZeroOneMatrixGoal hRaw)

theorem not_exactEdgeColoringGoal :
    ¬ ExactEdgeColoringGoal.{0, 0} := by
  intro hExact
  exact not_hallRealizationGoal
    (hallRealizationGoal_of_exactEdgeColoring hExact)

theorem not_rawExactEdgeColoringGoal :
    ¬ RawExactEdgeColoringGoal.{0, 0} := by
  intro hRaw
  exact not_rawZeroOneMatrixGoal
    (rawZeroOneMatrixGoal_of_rawExactEdgeColoringGoal hRaw)

theorem eraseLastHallCutsProperTokenQuotaSelectionGoal_of_compatibleDeWerraGoal
    (hDW : CompatibleDeWerraGoal.{uX, uC}) :
    EraseLastHallCutsProperTokenQuotaSelectionGoal.{uX, uC} :=
  (hallRealizationGoal_iff_eraseLastHallCutsProperTokenQuotaSelectionGoal).1
    (hallRealizationGoal_of_compatibleDeWerraGoal hDW)

theorem eraseLastHallCutsProperTokenQuotaSelectionGoal_of_compatibleZeroOneMatrixGoal
    (hMat : CompatibleZeroOneMatrixGoal.{uX, uC}) :
    EraseLastHallCutsProperTokenQuotaSelectionGoal.{uX, uC} :=
  (hallRealizationGoal_iff_eraseLastHallCutsProperTokenQuotaSelectionGoal).1
    (hallRealizationGoal_of_compatibleZeroOneMatrixGoal hMat)

theorem eraseLastHallCutsProperTokenQuotaSelectionGoal_of_rawZeroOneMatrixGoal
    (hRaw : RawZeroOneMatrixGoal.{uX, uC}) :
    EraseLastHallCutsProperTokenQuotaSelectionGoal.{uX, uC} :=
  (hallRealizationGoal_iff_eraseLastHallCutsProperTokenQuotaSelectionGoal).1
    (hallRealizationGoal_of_rawZeroOneMatrixGoal hRaw)

theorem rawZeroOneMatrixGoal_of_eraseLastHallCutsTokenLinearChoiceGoal
    (hToken : EraseLastHallCutsTokenLinearChoiceGoal.{uX, uC}) :
    RawZeroOneMatrixGoal.{uX, uC} :=
  rawZeroOneMatrixGoal_of_hallRealizationGoal
    (hallRealizationGoal_of_eraseLastHallCutsTokenLinearChoice hToken)

theorem rawZeroOneMatrixGoal_of_eraseLastHallCutsProperTokenLinearChoiceGoal
    (hProper : EraseLastHallCutsProperTokenLinearChoiceGoal.{uX, uC}) :
    RawZeroOneMatrixGoal.{uX, uC} :=
  rawZeroOneMatrixGoal_of_hallRealizationGoal
    (hallRealizationGoal_of_eraseLastHallCutsProperTokenLinearChoice hProper)

theorem rawZeroOneMatrixGoal_of_eraseLastHallCutsProperTokenQuotaSelectionGoal
    (hQuota : EraseLastHallCutsProperTokenQuotaSelectionGoal.{uX, uC}) :
    RawZeroOneMatrixGoal.{uX, uC} :=
  rawZeroOneMatrixGoal_of_eraseLastHallCutsProperTokenLinearChoiceGoal
    (eraseLastHallCutsProperTokenLinearChoiceGoal_of_quota hQuota)

theorem rawZeroOneMatrixGoal_iff_eraseLastHallCutsProperTokenQuotaSelectionGoal :
    RawZeroOneMatrixGoal.{uX, uC} ↔
      EraseLastHallCutsProperTokenQuotaSelectionGoal.{uX, uC} :=
  ⟨fun hRaw =>
      (hallRealizationGoal_iff_eraseLastHallCutsProperTokenQuotaSelectionGoal).1
        ((rawZeroOneMatrixGoal_iff_hallRealizationGoal).1 hRaw),
    rawZeroOneMatrixGoal_of_eraseLastHallCutsProperTokenQuotaSelectionGoal⟩

theorem rawZeroOneMatrixGoal_iff_eraseLastHallCutsTokenLinearChoiceGoal :
    RawZeroOneMatrixGoal.{uX, uC} ↔
      EraseLastHallCutsTokenLinearChoiceGoal.{uX, uC} :=
  ⟨fun hRaw =>
      eraseLastHallCutsTokenLinearChoiceGoal_of_hallRealization
        ((rawZeroOneMatrixGoal_iff_hallRealizationGoal).1 hRaw),
    rawZeroOneMatrixGoal_of_eraseLastHallCutsTokenLinearChoiceGoal⟩

theorem rawZeroOneMatrixGoal_iff_eraseLastHallCutsProperTokenLinearChoiceGoal :
    RawZeroOneMatrixGoal.{uX, uC} ↔
      EraseLastHallCutsProperTokenLinearChoiceGoal.{uX, uC} :=
  ⟨fun hRaw =>
      (hallRealizationGoal_iff_eraseLastHallCutsProperTokenLinearChoiceGoal).1
        ((rawZeroOneMatrixGoal_iff_hallRealizationGoal).1 hRaw),
    rawZeroOneMatrixGoal_of_eraseLastHallCutsProperTokenLinearChoiceGoal⟩

end FiniteHoffman
end ActiveHall
end RoundComposite
