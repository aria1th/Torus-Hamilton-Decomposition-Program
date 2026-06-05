import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.ZMod.Basic
import Shared.ReturnLift

/-!
# Comparison-switch calculus (cut-splice)

Formalization of the paper's cut-splice / packet-splice machinery (§3 Lemma 3.5,
§6 Lemma 6.13 `one-step-packet-splice` and Lemma 6.16 `flag-splicing-criterion`).

The core fact `oneStepPacketSplice` is **construction-agnostic**: it merges `q`
coset cycles into a single cycle, stated purely over a finite type with
`Equiv.Perm` and mathlib's `Equiv.Perm.IsCycleOn`. It is the single biggest
lever for closing the finite-anchor obligations (ledger holes H2·H3·H4·H6).

See `docs/P3_CUT_SPLICE_VERIFICATION_20260603.md`.
-/

namespace Shared
namespace SwitchCalculus

open Equiv (Perm)

variable {α : Type*}

/-! ### Bridge to the repository's single-cycle predicate -/

/-- A mathlib permutation cycle on the whole type gives the repository's
`IsSingleCycleMap` predicate for the underlying map. -/
theorem isSingleCycleMap_of_isCycleOn_univ [Finite α] (f : Perm α)
    (hf : f.IsCycleOn (Set.univ : Set α)) :
    Shared.IsSingleCycleMap f := by
  refine ⟨f.bijective, ?_⟩
  intro x y
  obtain ⟨n, hn⟩ := (hf.2 (by simp) (by simp : y ∈ (Set.univ : Set α))).exists_nat_pow_eq
  refine ⟨n, ?_⟩
  simpa using hn

/-- A repository single-cycle map gives a mathlib `IsCycleOn Set.univ` for the
permutation obtained from its bijectivity proof. -/
theorem isCycleOn_univ_of_isSingleCycleMap (f : α → α)
    (hf : Shared.IsSingleCycleMap f) :
    Equiv.Perm.IsCycleOn (Equiv.ofBijective f hf.1 : Perm α) (Set.univ : Set α) := by
  refine ⟨(Equiv.ofBijective f hf.1 : Perm α).bijective.bijOn_univ, ?_⟩
  intro x _ y _
  obtain ⟨n, hn⟩ := hf.2 x y
  refine ⟨(n : ℤ), ?_⟩
  simpa [zpow_natCast] using hn

/-- On a finite type, mathlib's `IsCycleOn Set.univ` for the associated
permutation is equivalent to the repository's `IsSingleCycleMap`. -/
theorem isCycleOn_univ_iff_isSingleCycleMap [Finite α] (f : α → α)
    (hf : Function.Bijective f) :
    Equiv.Perm.IsCycleOn (Equiv.ofBijective f hf : Perm α) (Set.univ : Set α) ↔
      Shared.IsSingleCycleMap f := by
  constructor
  · intro hcycle
    simpa using
      isSingleCycleMap_of_isCycleOn_univ (Equiv.ofBijective f hf : Perm α) hcycle
  · intro hsingle
    exact isCycleOn_univ_of_isSingleCycleMap f hsingle

/-- A permutation is a single cycle on `s` as soon as it is bijective on `s` and
every point of `s` is in the same cycle as one fixed base point `a ∈ s`. This is
the convenient constructor for `Equiv.Perm.IsCycleOn`: it removes the universal
quantifier over *pairs* by routing through a base point and `SameCycle`'s
transitivity. -/
theorem isCycleOn_of_sameCycle_base
    (f : Perm α) (s : Set α) (hbij : Set.BijOn f s s)
    {a : α} (_ha : a ∈ s) (hreach : ∀ b ∈ s, f.SameCycle a b) :
    f.IsCycleOn s := by
  refine ⟨hbij, ?_⟩
  intro x hx y hy
  exact (hreach x hx).symm.trans (hreach y hy)

/-- Inside its own coset, away from that coset's cut tail, the spliced
permutation `R'` agrees with the original return `R`. (Disjointness rules out
the other tails.) -/
theorem splice_eq_orig_off_tail
    {q : ℕ} (R R' : Perm α) (C : ZMod q → Set α) (a h : ZMod q → α)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hmem : ∀ j, a j ∈ C j ∧ h j ∈ C j)
    (hRest : ∀ x, (∀ k, x ≠ a k) → R' x = R x)
    {j : ZMod q} {x : α} (hx : x ∈ C j) (hxa : x ≠ a j) :
    R' x = R x := by
  apply hRest
  intro k
  rcases eq_or_ne k j with hk | hk
  · exact hk ▸ hxa
  · intro hxak
    have hxk : x ∈ C k := by rw [hxak]; exact (hmem k).1
    exact Set.disjoint_left.mp (hdisj j k (Ne.symm hk)) hx hxk

/-- The spliced permutation keeps the union of cosets invariant: a non-tail
point stays in its coset (via `R`), and `a j` is sent to `h (j+1) ∈ C (j+1)`. -/
theorem splice_mapsTo
    {q : ℕ} [NeZero q] (R R' : Perm α) (C : ZMod q → Set α) (a h : ZMod q → α)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hmem : ∀ j, a j ∈ C j ∧ h j ∈ C j)
    (hCyc : ∀ j, R.IsCycleOn (C j))
    (hSplice : ∀ j, R' (a j) = h (j + 1))
    (hRest : ∀ x, (∀ k, x ≠ a k) → R' x = R x) :
    Set.MapsTo R' (⋃ j, C j) (⋃ j, C j) := by
  intro x hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨j, hxj⟩ := hx
  rw [Set.mem_iUnion]
  rcases eq_or_ne x (a j) with hxa | hxa
  · refine ⟨j + 1, ?_⟩
    rw [hxa, hSplice j]
    exact (hmem (j + 1)).2
  · refine ⟨j, ?_⟩
    rw [splice_eq_orig_off_tail R R' C a h hdisj hmem hRest hxj hxa]
    exact (hCyc j).1.mapsTo hxj

/-- **Cut-splice orbit sweep** (the core of Lemma 6.13). Inside one coset, the
spliced orbit started at that coset's head `h j` reaches every point of `C j`
(it follows `R` until it exits at the tail `a j`). -/
theorem within_coset_reach
    [Finite α] {q : ℕ} [NeZero q]
    (R R' : Perm α) (C : ZMod q → Set α) (a h : ZMod q → α)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hmem : ∀ j, a j ∈ C j ∧ h j ∈ C j)
    (hHead : ∀ j, R (a j) = h j)
    (hCyc : ∀ j, R.IsCycleOn (C j))
    (hRest : ∀ x, (∀ k, x ≠ a k) → R' x = R x)
    (j : ZMod q) {b : α} (hb : b ∈ C j) :
    R'.SameCycle (h j) b := by
  classical
  let s : Finset α := (Set.toFinite (C j)).toFinset
  have hCycS : R.IsCycleOn (s : Set α) := by
    simpa [s] using hCyc j
  have hh : h j ∈ s := by
    simpa [s] using (hmem j).2
  have hbS : b ∈ s := by
    simpa [s] using hb
  obtain ⟨n, hnlt, hn⟩ := hCycS.exists_pow_eq hh hbS
  have hprefix : ∀ m ≤ n, R'.SameCycle (h j) ((R ^ m) (h j)) := by
    intro m hm
    induction m with
    | zero =>
        simpa using Equiv.Perm.SameCycle.refl R' (h j)
    | succ m ih =>
        have hm_le : m ≤ n := Nat.le_of_succ_le hm
        have hm_lt : m < n := Nat.lt_of_succ_le hm
        have hxmem : (R ^ m) (h j) ∈ C j := by
          exact (hCyc j).1.mapsTo.perm_pow m (hmem j).2
        have hsucc :
            (R ^ (m + 1)) (h j) = R ((R ^ m) (h j)) := by
          simp [pow_succ']
        have hxne : (R ^ m) (h j) ≠ a j := by
          intro hxa
          have hreturn : (R ^ (m + 1)) (h j) = h j := by
            rw [hsucc, hxa, hHead j]
          have hdiv : s.card ∣ m + 1 :=
            (hCycS.pow_apply_eq (a := h j) hh (n := m + 1)).mp hreturn
          have hpos : 0 < m + 1 := Nat.succ_pos m
          have hltcard : m + 1 < s.card := lt_of_le_of_lt hm hnlt
          exact (Nat.not_dvd_of_pos_of_lt hpos hltcard) hdiv
        have hstepEq : R' ((R ^ m) (h j)) = R ((R ^ m) (h j)) :=
          splice_eq_orig_off_tail R R' C a h hdisj hmem hRest hxmem hxne
        have hstep :
            R'.SameCycle ((R ^ m) (h j)) ((R ^ (m + 1)) (h j)) := by
          refine ⟨1, ?_⟩
          rw [zpow_one, hstepEq, hsucc]
        exact (ih hm_le).trans hstep
  exact (hprefix n le_rfl).trans (hn.sameCycle R')

/-- **One-step packet splice** (paper Lemma 6.13 `lem:one-step-packet-splice`).

`R` is a return permutation that is a single cycle on each of the `q` cosets
`C j` (pairwise disjoint). Each coset carries a cut tail `a j` and its old head
`h j = R (a j)`. The spliced permutation `R'` keeps every other arc but reroutes
each `a j` to the *next* coset's old head, `R' (a j) = h (j+1)`. Then `R'` is a
single cycle on the union `⋃ j, C j`.

This is the cut-splice (§3 Lemma 3.5) specialized to the cyclic-coset setting.

Proof outline: with `c j := (C j).ncard`,
* away from `a j`, `R' = R` on `C j` (`splice_eq_orig_off_tail`), and
  `a j = R^[c j - 1] (h j)` (since `R^[c j] (a j) = a j` and `h j = R (a j)`);
* hence `R'^[k] (h j) = R^[k] (h j)` for `k < c j`, so the `R'`-orbit of `h j`
  sweeps all of `C j` and `R'^[c j] (h j) = R' (a j) = h (j+1)`;
* chaining the cosets in cyclic order, every point of `⋃ C j` lies in the
  `R'`-orbit of `h 0`, and `R'` maps the union into itself; conclude via
  `isCycleOn_of_sameCycle_base`.
-/
theorem oneStepPacketSplice
    [Finite α]
    {q : ℕ} [NeZero q]
    (R R' : Perm α)
    (C : ZMod q → Set α) (a h : ZMod q → α)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hmem : ∀ j, a j ∈ C j ∧ h j ∈ C j)
    (hHead : ∀ j, R (a j) = h j)
    (hCyc : ∀ j, R.IsCycleOn (C j))
    (hSplice : ∀ j, R' (a j) = h (j + 1))
    (hRest : ∀ x, (∀ k, x ≠ a k) → R' x = R x) :
    R'.IsCycleOn (⋃ j, C j) := by
  have hmaps : Set.MapsTo R' (⋃ j, C j) (⋃ j, C j) :=
    splice_mapsTo R R' C a h hdisj hmem hCyc hSplice hRest
  have hfin : (⋃ j, C j).Finite := Set.toFinite _
  have hbij : Set.BijOn R' (⋃ j, C j) (⋃ j, C j) :=
    (hfin.injOn_iff_bijOn_of_mapsTo hmaps).mp (R'.injective.injOn)
  refine isCycleOn_of_sameCycle_base R' _ hbij (a := h 0)
    (Set.mem_iUnion.2 ⟨0, (hmem 0).2⟩) ?_
  -- The `R'`-orbit of `h 0` reaches every point: sweep each coset from its head
  -- (`within_coset_reach`) and chain the heads around the cyclic coset order.
  have hStep : ∀ j : ZMod q, R'.SameCycle (h j) (h (j + 1)) := by
    intro j
    have hPa : R'.SameCycle (h j) (a j) :=
      within_coset_reach R R' C a h hdisj hmem hHead hCyc hRest j (hmem j).1
    have hone : R'.SameCycle (a j) (h (j + 1)) := ⟨1, by simpa using hSplice j⟩
    exact hPa.trans hone
  have hHeadChain : ∀ j : ZMod q, R'.SameCycle (h 0) (h j) := by
    have hnat : ∀ n : ℕ, R'.SameCycle (h 0) (h (n : ZMod q)) := by
      intro n
      induction n with
      | zero => simpa using Equiv.Perm.SameCycle.refl R' (h 0)
      | succ n ih =>
          have hcast : ((n + 1 : ℕ) : ZMod q) = (n : ZMod q) + 1 := by push_cast; ring
          rw [hcast]
          exact ih.trans (hStep (n : ZMod q))
    intro j
    rw [← ZMod.natCast_zmod_val j]
    exact hnat (ZMod.val j)
  intro b hb
  rw [Set.mem_iUnion] at hb
  obtain ⟨j, hbj⟩ := hb
  exact (hHeadChain j).trans
    (within_coset_reach R R' C a h hdisj hmem hHead hCyc hRest j hbj)

/-- `oneStepPacketSplice`, repackaged in the repository's global
`IsSingleCycleMap` interface when the coset packet covers the whole type. -/
theorem oneStepPacketSplice_singleCycleMap
    [Finite α]
    {q : ℕ} [NeZero q]
    (R R' : Perm α)
    (C : ZMod q → Set α) (a h : ZMod q → α)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hmem : ∀ j, a j ∈ C j ∧ h j ∈ C j)
    (hHead : ∀ j, R (a j) = h j)
    (hCyc : ∀ j, R.IsCycleOn (C j))
    (hSplice : ∀ j, R' (a j) = h (j + 1))
    (hRest : ∀ x, (∀ k, x ≠ a k) → R' x = R x)
    (hcover : (⋃ j, C j) = Set.univ) :
    Shared.IsSingleCycleMap R' := by
  apply isSingleCycleMap_of_isCycleOn_univ R'
  simpa [hcover] using
    oneStepPacketSplice R R' C a h hdisj hmem hHead hCyc hSplice hRest

structure OneStepPacketSpliceCertificate {q : ℕ}
    (R R' : Perm α) (C : ZMod q → Set α) (a h : ZMod q → α) :
    Prop where
  pairwiseDisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j)
  mem : ∀ j, a j ∈ C j ∧ h j ∈ C j
  head : ∀ j, R (a j) = h j
  cycles : ∀ j, R.IsCycleOn (C j)
  splice : ∀ j, R' (a j) = h (j + 1)
  rest : ∀ x, (∀ k, x ≠ a k) → R' x = R x

theorem OneStepPacketSpliceCertificate.isCycleOn
    [Finite α] {q : ℕ} [NeZero q]
    {R R' : Perm α} {C : ZMod q → Set α} {a h : ZMod q → α}
    (cert : OneStepPacketSpliceCertificate R R' C a h) :
    R'.IsCycleOn (⋃ j, C j) :=
  oneStepPacketSplice R R' C a h cert.pairwiseDisjoint cert.mem cert.head
    cert.cycles cert.splice cert.rest

theorem OneStepPacketSpliceCertificate.isSingleCycleMap
    [Finite α] {q : ℕ} [NeZero q]
    {R R' : Perm α} {C : ZMod q → Set α} {a h : ZMod q → α}
    (cert : OneStepPacketSpliceCertificate R R' C a h)
    (cover : (⋃ j, C j) = Set.univ) :
    Shared.IsSingleCycleMap R' :=
  oneStepPacketSplice_singleCycleMap R R' C a h cert.pairwiseDisjoint
    cert.mem cert.head cert.cycles cert.splice cert.rest cover

/-! ### Local and parallel packet splicing -/

/-- Local version of `splice_eq_orig_off_tail`: it only asks for `R' = R` on
the packet support, away from the packet's own tails. This is the form needed
when several disjoint packets are spliced in parallel. -/
theorem splice_eq_orig_off_tail_on
    {q : ℕ} (R R' : Perm α) (C : ZMod q → Set α) (a h : ZMod q → α)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hmem : ∀ j, a j ∈ C j ∧ h j ∈ C j)
    (hRest : ∀ x, x ∈ (⋃ j, C j) → (∀ k, x ≠ a k) → R' x = R x)
    {j : ZMod q} {x : α} (hx : x ∈ C j) (hxa : x ≠ a j) :
    R' x = R x := by
  apply hRest
  · exact Set.mem_iUnion.2 ⟨j, hx⟩
  · intro k
    rcases eq_or_ne k j with hk | hk
    · exact hk ▸ hxa
    · intro hxak
      have hxk : x ∈ C k := by rw [hxak]; exact (hmem k).1
      exact Set.disjoint_left.mp (hdisj j k (Ne.symm hk)) hx hxk

/-- Local version of `splice_mapsTo`. -/
theorem splice_mapsTo_on
    {q : ℕ} [NeZero q] (R R' : Perm α) (C : ZMod q → Set α) (a h : ZMod q → α)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hmem : ∀ j, a j ∈ C j ∧ h j ∈ C j)
    (hCyc : ∀ j, R.IsCycleOn (C j))
    (hSplice : ∀ j, R' (a j) = h (j + 1))
    (hRest : ∀ x, x ∈ (⋃ j, C j) → (∀ k, x ≠ a k) → R' x = R x) :
    Set.MapsTo R' (⋃ j, C j) (⋃ j, C j) := by
  intro x hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨j, hxj⟩ := hx
  rw [Set.mem_iUnion]
  rcases eq_or_ne x (a j) with hxa | hxa
  · refine ⟨j + 1, ?_⟩
    rw [hxa, hSplice j]
    exact (hmem (j + 1)).2
  · refine ⟨j, ?_⟩
    rw [splice_eq_orig_off_tail_on R R' C a h hdisj hmem hRest hxj hxa]
    exact (hCyc j).1.mapsTo hxj

/-- Local version of `within_coset_reach`, suitable for one packet inside a
parallel splice layer. -/
theorem within_coset_reach_on
    [Finite α] {q : ℕ} [NeZero q]
    (R R' : Perm α) (C : ZMod q → Set α) (a h : ZMod q → α)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hmem : ∀ j, a j ∈ C j ∧ h j ∈ C j)
    (hHead : ∀ j, R (a j) = h j)
    (hCyc : ∀ j, R.IsCycleOn (C j))
    (hRest : ∀ x, x ∈ (⋃ j, C j) → (∀ k, x ≠ a k) → R' x = R x)
    (j : ZMod q) {b : α} (hb : b ∈ C j) :
    R'.SameCycle (h j) b := by
  classical
  let s : Finset α := (Set.toFinite (C j)).toFinset
  have hCycS : R.IsCycleOn (s : Set α) := by
    simpa [s] using hCyc j
  have hh : h j ∈ s := by
    simpa [s] using (hmem j).2
  have hbS : b ∈ s := by
    simpa [s] using hb
  obtain ⟨n, hnlt, hn⟩ := hCycS.exists_pow_eq hh hbS
  have hprefix : ∀ m ≤ n, R'.SameCycle (h j) ((R ^ m) (h j)) := by
    intro m hm
    induction m with
    | zero =>
        simpa using Equiv.Perm.SameCycle.refl R' (h j)
    | succ m ih =>
        have hm_le : m ≤ n := Nat.le_of_succ_le hm
        have hm_lt : m < n := Nat.lt_of_succ_le hm
        have hxmem : (R ^ m) (h j) ∈ C j := by
          exact (hCyc j).1.mapsTo.perm_pow m (hmem j).2
        have hsucc :
            (R ^ (m + 1)) (h j) = R ((R ^ m) (h j)) := by
          simp [pow_succ']
        have hxne : (R ^ m) (h j) ≠ a j := by
          intro hxa
          have hreturn : (R ^ (m + 1)) (h j) = h j := by
            rw [hsucc, hxa, hHead j]
          have hdiv : s.card ∣ m + 1 :=
            (hCycS.pow_apply_eq (a := h j) hh (n := m + 1)).mp hreturn
          have hpos : 0 < m + 1 := Nat.succ_pos m
          have hltcard : m + 1 < s.card := lt_of_le_of_lt hm hnlt
          exact (Nat.not_dvd_of_pos_of_lt hpos hltcard) hdiv
        have hstepEq : R' ((R ^ m) (h j)) = R ((R ^ m) (h j)) :=
          splice_eq_orig_off_tail_on R R' C a h hdisj hmem hRest hxmem hxne
        have hstep :
            R'.SameCycle ((R ^ m) (h j)) ((R ^ (m + 1)) (h j)) := by
          refine ⟨1, ?_⟩
          rw [zpow_one, hstepEq, hsucc]
        exact (ih hm_le).trans hstep
  exact (hprefix n le_rfl).trans (hn.sameCycle R')

/-- Local version of `oneStepPacketSplice`. It is the same one-packet merge
criterion, but the unchanged-edge hypothesis is required only on the packet
support. -/
theorem oneStepPacketSpliceOn
    [Finite α]
    {q : ℕ} [NeZero q]
    (R R' : Perm α)
    (C : ZMod q → Set α) (a h : ZMod q → α)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hmem : ∀ j, a j ∈ C j ∧ h j ∈ C j)
    (hHead : ∀ j, R (a j) = h j)
    (hCyc : ∀ j, R.IsCycleOn (C j))
    (hSplice : ∀ j, R' (a j) = h (j + 1))
    (hRest : ∀ x, x ∈ (⋃ j, C j) → (∀ k, x ≠ a k) → R' x = R x) :
    R'.IsCycleOn (⋃ j, C j) := by
  have hmaps : Set.MapsTo R' (⋃ j, C j) (⋃ j, C j) :=
    splice_mapsTo_on R R' C a h hdisj hmem hCyc hSplice hRest
  have hfin : (⋃ j, C j).Finite := Set.toFinite _
  have hbij : Set.BijOn R' (⋃ j, C j) (⋃ j, C j) :=
    (hfin.injOn_iff_bijOn_of_mapsTo hmaps).mp (R'.injective.injOn)
  refine isCycleOn_of_sameCycle_base R' _ hbij (a := h 0)
    (Set.mem_iUnion.2 ⟨0, (hmem 0).2⟩) ?_
  have hStep : ∀ j : ZMod q, R'.SameCycle (h j) (h (j + 1)) := by
    intro j
    have hPa : R'.SameCycle (h j) (a j) :=
      within_coset_reach_on R R' C a h hdisj hmem hHead hCyc hRest j (hmem j).1
    have hone : R'.SameCycle (a j) (h (j + 1)) := ⟨1, by simpa using hSplice j⟩
    exact hPa.trans hone
  have hHeadChain : ∀ j : ZMod q, R'.SameCycle (h 0) (h j) := by
    have hnat : ∀ n : ℕ, R'.SameCycle (h 0) (h (n : ZMod q)) := by
      intro n
      induction n with
      | zero => simpa using Equiv.Perm.SameCycle.refl R' (h 0)
      | succ n ih =>
          have hcast : ((n + 1 : ℕ) : ZMod q) = (n : ZMod q) + 1 := by push_cast; ring
          rw [hcast]
          exact ih.trans (hStep (n : ZMod q))
    intro j
    rw [← ZMod.natCast_zmod_val j]
    exact hnat (ZMod.val j)
  intro b hb
  rw [Set.mem_iUnion] at hb
  obtain ⟨j, hbj⟩ := hb
  exact (hHeadChain j).trans
    (within_coset_reach_on R R' C a h hdisj hmem hHead hCyc hRest j hbj)

/-- One layer of the flag-splicing criterion: if every target cell `D i` is
split into cyclic old cells `C i j`, and all packets are spliced in parallel
with pairwise disjoint target supports, then the new return is a cycle on every
target cell. Iterating this layer over a flag gives the paper's
`flag-splicing-criterion`. -/
theorem flagSplicingCriterion
    [Finite α]
    {ι : Type*}
    (q : ι → ℕ) (hne : ∀ i : ι, NeZero (q i))
    (R R' : Perm α)
    (D : ι → Set α)
    (C : ∀ i : ι, ZMod (q i) → Set α)
    (a h : ∀ i : ι, ZMod (q i) → α)
    (hcell : ∀ i : ι, D i = ⋃ j, C i j)
    (hpacketDisj : ∀ i i' : ι, i ≠ i' → Disjoint (D i) (D i'))
    (hdisj : ∀ i : ι, ∀ j k : ZMod (q i), j ≠ k → Disjoint (C i j) (C i k))
    (hmem : ∀ i : ι, ∀ j : ZMod (q i), a i j ∈ C i j ∧ h i j ∈ C i j)
    (hHead : ∀ i : ι, ∀ j : ZMod (q i), R (a i j) = h i j)
    (hCyc : ∀ i : ι, ∀ j : ZMod (q i), R.IsCycleOn (C i j))
    (hSplice : ∀ i : ι, ∀ j : ZMod (q i), R' (a i j) = h i (j + 1))
    (hRest :
      ∀ x, x ∈ (⋃ i, D i) →
        (∀ i : ι, ∀ j : ZMod (q i), x ≠ a i j) → R' x = R x) :
    ∀ i : ι, R'.IsCycleOn (D i) := by
  intro i
  haveI : NeZero (q i) := hne i
  have hRest_i :
      ∀ x, x ∈ (⋃ j, C i j) → (∀ k : ZMod (q i), x ≠ a i k) → R' x = R x := by
    intro x hx hxnot
    apply hRest x
    · exact Set.mem_iUnion.2 ⟨i, by simpa [hcell i] using hx⟩
    · intro i' j'
      by_cases hii' : i' = i
      · subst i'
        exact hxnot j'
      · intro hxa'
        have hxD : x ∈ D i := by
          simpa [hcell i] using hx
        have hxD' : x ∈ D i' := by
          rw [hxa']
          rw [hcell i']
          exact Set.mem_iUnion.2 ⟨j', (hmem i' j').1⟩
        exact Set.disjoint_left.mp (hpacketDisj i i' (Ne.symm hii')) hxD hxD'
  have hcycle :
      R'.IsCycleOn (⋃ j, C i j) :=
    oneStepPacketSpliceOn R R' (C i) (a i) (h i)
      (hdisj i) (hmem i) (hHead i) (hCyc i) (hSplice i) hRest_i
  simpa [hcell i] using hcycle

/-- `flagSplicingCriterion` repackaged for the final flag layer when one target
cell is the whole type. -/
theorem flagSplicingCriterion_singleCycleMap
    [Finite α]
    {ι : Type*}
    (q : ι → ℕ) (hne : ∀ i : ι, NeZero (q i))
    (R R' : Perm α)
    (D : ι → Set α)
    (C : ∀ i : ι, ZMod (q i) → Set α)
    (a h : ∀ i : ι, ZMod (q i) → α)
    (hcell : ∀ i : ι, D i = ⋃ j, C i j)
    (hpacketDisj : ∀ i i' : ι, i ≠ i' → Disjoint (D i) (D i'))
    (hdisj : ∀ i : ι, ∀ j k : ZMod (q i), j ≠ k → Disjoint (C i j) (C i k))
    (hmem : ∀ i : ι, ∀ j : ZMod (q i), a i j ∈ C i j ∧ h i j ∈ C i j)
    (hHead : ∀ i : ι, ∀ j : ZMod (q i), R (a i j) = h i j)
    (hCyc : ∀ i : ι, ∀ j : ZMod (q i), R.IsCycleOn (C i j))
    (hSplice : ∀ i : ι, ∀ j : ZMod (q i), R' (a i j) = h i (j + 1))
    (hRest :
      ∀ x, x ∈ (⋃ i, D i) →
        (∀ i : ι, ∀ j : ZMod (q i), x ≠ a i j) → R' x = R x)
    (top : ι) (hcover : D top = Set.univ) :
    Shared.IsSingleCycleMap R' := by
  apply isSingleCycleMap_of_isCycleOn_univ R'
  have hcycles :=
    flagSplicingCriterion q hne R R' D C a h hcell hpacketDisj hdisj
      hmem hHead hCyc hSplice hRest
  simpa [hcover] using hcycles top

structure FlagSplicingCertificate {ι : Type*}
    (q : ι → ℕ) (R R' : Perm α)
    (D : ι → Set α)
    (C : ∀ i : ι, ZMod (q i) → Set α)
    (a h : ∀ i : ι, ZMod (q i) → α) : Prop where
  neZero : ∀ i : ι, NeZero (q i)
  cell : ∀ i : ι, D i = ⋃ j, C i j
  packetDisjoint : ∀ i i' : ι, i ≠ i' → Disjoint (D i) (D i')
  cosetDisjoint :
    ∀ i : ι, ∀ j k : ZMod (q i),
      j ≠ k → Disjoint (C i j) (C i k)
  mem :
    ∀ i : ι, ∀ j : ZMod (q i), a i j ∈ C i j ∧ h i j ∈ C i j
  head : ∀ i : ι, ∀ j : ZMod (q i), R (a i j) = h i j
  cycles : ∀ i : ι, ∀ j : ZMod (q i), R.IsCycleOn (C i j)
  splice : ∀ i : ι, ∀ j : ZMod (q i), R' (a i j) = h i (j + 1)
  rest :
    ∀ x, x ∈ (⋃ i, D i) →
      (∀ i : ι, ∀ j : ZMod (q i), x ≠ a i j) → R' x = R x

theorem FlagSplicingCertificate.isCycleOn
    [Finite α] {ι : Type*}
    {q : ι → ℕ} {R R' : Perm α}
    {D : ι → Set α}
    {C : ∀ i : ι, ZMod (q i) → Set α}
    {a h : ∀ i : ι, ZMod (q i) → α}
    (cert : FlagSplicingCertificate q R R' D C a h) :
    ∀ i : ι, R'.IsCycleOn (D i) :=
  flagSplicingCriterion q cert.neZero R R' D C a h cert.cell
    cert.packetDisjoint cert.cosetDisjoint cert.mem cert.head cert.cycles
    cert.splice cert.rest

theorem FlagSplicingCertificate.isSingleCycleMap
    [Finite α] {ι : Type*}
    {q : ι → ℕ} {R R' : Perm α}
    {D : ι → Set α}
    {C : ∀ i : ι, ZMod (q i) → Set α}
    {a h : ∀ i : ι, ZMod (q i) → α}
    (cert : FlagSplicingCertificate q R R' D C a h)
    (top : ι) (cover : D top = Set.univ) :
    Shared.IsSingleCycleMap R' :=
  flagSplicingCriterion_singleCycleMap q cert.neZero R R' D C a h cert.cell
    cert.packetDisjoint cert.cosetDisjoint cert.mem cert.head cert.cycles
    cert.splice cert.rest top cover

end SwitchCalculus
end Shared
