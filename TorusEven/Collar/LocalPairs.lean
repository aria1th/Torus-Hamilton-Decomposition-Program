-- STATUS: main-path
import TorusEven.Collar.ParityJoin
import TorusEven.Collar.BalancedOrientation

namespace TorusEven.Collar

structure LocalPairs {Ω : Type*} (A : Finset Ω) where
  count : ℕ
  endpoint : Fin count × Bool ↪ Ω
  mem_endpoint : ∀ p, endpoint p ∈ A

namespace LocalPairs

variable {Ω : Type*} {A : Finset Ω} (P : LocalPairs A)

def reverse (flip : Fin P.count → Bool) : LocalPairs A where
  count := P.count
  endpoint := (Equiv.prodCongrRight (fun i =>
    if flip i then Equiv.boolNot else Equiv.refl Bool)).toEmbedding.trans P.endpoint
  mem_endpoint _ := P.mem_endpoint _

@[simp] theorem reverse_endpoint (flip : Fin P.count → Bool) (i : Fin P.count) (b : Bool) :
    (P.reverse flip).endpoint (i, b) = P.endpoint (i, if flip i then !b else b) := by
  change P.endpoint (i, (if flip i then Equiv.boolNot else Equiv.refl Bool) b) = _
  cases flip i <;> simp

def support : Finset Ω := Finset.univ.map P.endpoint

@[simp] theorem mem_support {x : Ω} : x ∈ P.support ↔ ∃ p, P.endpoint p = x := by
  simp [support]

theorem support_subset : P.support ⊆ A := by
  rintro x hx
  obtain ⟨p, rfl⟩ := P.mem_support.mp hx
  exact P.mem_endpoint p

@[simp] theorem card_support : P.support.card = 2 * P.count := by
  simp [support, Fintype.card_prod, mul_comm]

theorem count_le : 2 * P.count ≤ A.card := by
  simpa using Finset.card_le_card P.support_subset

def divergence [DecidableEq Ω] (x : Ω) : ℤ :=
  ∑ i : Fin P.count, ((if P.endpoint (i, true) = x then 1 else 0) -
    (if P.endpoint (i, false) = x then 1 else 0))

end LocalPairs

namespace Incidence

variable {B Ω : Type*} [Fintype B] [Finite Ω] [DecidableEq Ω]

theorem exists_directed_pairs_on (A : B → Finset Ω) (target : Finset Ω)
    (hEven : EvenOnComponents A target) :
    ∃ P : ∀ b, LocalPairs (A b),
      (∀ x ∈ target, (∑ b, (P b).divergence x) = 1 ∨ (∑ b, (P b).divergence x) = -1) ∧
      ∀ x ∉ target, (∑ b, (P b).divergence x) = 0 := by
  classical
  obtain ⟨T, hT, heven, hparity⟩ := exists_parity_join_on A target hEven
  choose n hn using heven
  have hcard (b : B) : Fintype.card (Fin (n b) × Bool) = Fintype.card (T b) := by
    simp [Fintype.card_prod, hn, mul_two]
  let e (b : B) : Fin (n b) × Bool ≃ T b := Fintype.equivOfCardEq (hcard b)
  let P (b : B) : LocalPairs (A b) :=
    ⟨n b, (e b).toEmbedding.trans (Function.Embedding.subtype _), fun p => hT b (e b p).property⟩
  let l : (Σ b, Fin (n b)) → Ω := fun p => (e p.1 (p.2, false)).val
  let r : (Σ b, Fin (n b)) → Ω := fun p => (e p.1 (p.2, true)).val
  have hdegree (x : Ω) : Multigraph.degree l r x =
      (Finset.univ.filter (fun b => x ∈ T b)).card := by
    simp only [Multigraph.degree, Fintype.sum_sigma, Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    calc
      (∑ i : Fin (n b), ((if l ⟨b, i⟩ = x then 1 else 0) +
          (if r ⟨b, i⟩ = x then 1 else 0))) =
          ∑ p : Fin (n b) × Bool, if (e b p).val = x then 1 else 0 := by
        rw [Fintype.sum_prod_type]
        simp only [Fintype.sum_bool, l, r, add_comm]
      _ = ∑ p : T b, if p.val = x then 1 else 0 :=
        (e b).sum_comp (fun p : T b => if p.val = x then (1 : ℕ) else 0)
      _ = if x ∈ T b then 1 else 0 := by
        rw [Finset.sum_coe_sort (T b) (fun y => if y = x then (1 : ℕ) else 0)]
        simp
  obtain ⟨u, w, hor, hdiv, hzero⟩ := Multigraph.exists_mixed_orientation l r target
    (fun x => by rw [hdegree]; exact hparity x)
  let flip (b : B) (i : Fin (n b)) : Bool := decide (u ⟨b, i⟩ ≠ l ⟨b, i⟩)
  let Q (b : B) := (P b).reverse (flip b)
  have hends (b : B) (i : Fin (n b)) :
      (Q b).endpoint (i, false) = u ⟨b, i⟩ ∧ (Q b).endpoint (i, true) = w ⟨b, i⟩ := by
    have hne : l ⟨b, i⟩ ≠ r ⟨b, i⟩ := by
      intro h
      have h' := (e b).injective (Subtype.ext h)
      exact Bool.false_ne_true (congrArg Prod.snd h')
    rcases hor ⟨b, i⟩ with ⟨hu, hw⟩ | ⟨hu, hw⟩
    · simp [Q, P, LocalPairs.reverse_endpoint, flip, hu, hw, l, r]
    · have hne' : r ⟨b, i⟩ ≠ l ⟨b, i⟩ := hne.symm
      simp only [Q, LocalPairs.reverse_endpoint, flip, hu, ne_eq, hne', not_false_eq_true,
        decide_true, if_true, Bool.not_false, Bool.not_true]
      exact ⟨rfl, hw.symm⟩
  refine ⟨Q, ?_, ?_⟩
  · intro x hx
    simpa only [LocalPairs.divergence, Multigraph.divergence, Fintype.sum_sigma,
      (hends _ _).1, (hends _ _).2] using hdiv x hx
  · intro x hx
    simpa only [LocalPairs.divergence, Multigraph.divergence, Fintype.sum_sigma,
      (hends _ _).1, (hends _ _).2] using hzero x hx

theorem exists_directed_pairs (A : B → Finset Ω) (hEven : EvenComponents A) :
    ∃ P : ∀ b, LocalPairs (A b), ∀ x,
      (∑ b, ∑ i : Fin (P b).count,
        ((if (P b).endpoint (i, true) = x then (1 : ℤ) else 0) -
          (if (P b).endpoint (i, false) = x then 1 else 0))) = 1 ∨
      (∑ b, ∑ i : Fin (P b).count,
        ((if (P b).endpoint (i, true) = x then (1 : ℤ) else 0) -
          (if (P b).endpoint (i, false) = x then 1 else 0))) = -1 := by
  classical
  letI := Fintype.ofFinite Ω
  obtain ⟨P, hP, _⟩ := exists_directed_pairs_on A Finset.univ
    ((evenOnComponents_univ A).mpr hEven)
  refine ⟨P, fun x => ?_⟩
  simpa only [LocalPairs.divergence] using hP x (Finset.mem_univ x)

end Incidence

end TorusEven.Collar
