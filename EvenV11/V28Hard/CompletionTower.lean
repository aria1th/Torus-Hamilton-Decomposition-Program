import EvenV11.EndpointCompletion

/-!
# Hard slot H6 (E2): towers of completion-carry coordinates

The one-coordinate machinery of `EvenV11.EndpointCompletion` promotes a
single-cycle base step together with a completion-carry certificate to a
single cycle on `Base × ZMod m`.  This file iterates that step: a
`CompletionTower` carries `r` certificates, the `k`-th one living over the
skew-product space built from the first `k` coordinates, and `towerMap`
is the corresponding `r`-fold iterated additive skew map.

The enabling new tool is the converse rank lemma
`rankEquiv_of_singleCycle`: a single-cycle map on a finite type of
cardinality `N` admits a `ZMod N`-valued rank enumeration that increases
by one along the map.  This converts the single-cycle conclusion of one
tower level back into the rank-equivalence hypothesis demanded by
`completionCarryCertificate_singleCycle` at the next level, so the tower
closes by induction on `r`.

A sanity instance ties one tower step back to the existing `b = 4`
first-completion one-point certificate.
-/

/- The structure `CompletionTower` deliberately shares its name with this
file's namespace; the duplicate-namespace lint is therefore expected. -/
set_option linter.dupNamespace false

namespace EvenV11
namespace V28Hard
namespace CompletionTower

/-! ## Part 1: rank enumeration from a single cycle -/

/-- If two iterates of an injective map agree at a point, the difference
iterate fixes that point. -/
private theorem iterate_sub_fixed {X : Type*} (f : X → X)
    (hinj : Function.Injective f) (x₀ : X) {a b : Nat} (hab : a ≤ b)
    (h : f^[b] x₀ = f^[a] x₀) :
    f^[b - a] x₀ = x₀ := by
  apply hinj.iterate a
  calc
    f^[a] (f^[b - a] x₀) = f^[a + (b - a)] x₀ :=
      (Function.iterate_add_apply f a (b - a) x₀).symm
    _ = f^[b] x₀ := by rw [Nat.add_sub_cancel' hab]
    _ = f^[a] x₀ := h

/-- Converse rank lemma: a single-cycle map on a finite type of
cardinality `N` admits a `ZMod N` rank enumeration stepping by `+1`.
This is the converse of `Shared.single_cycle_of_zmod_rank_equiv`. -/
theorem rankEquiv_of_singleCycle {X : Type*} [Finite X] {N : Nat} [NeZero N]
    (f : X → X) (hf : Shared.IsSingleCycleMap f) (hcard : Nat.card X = N) :
    ∃ rank : X ≃ ZMod N, ∀ x, rank (f x) = rank x + 1 := by
  have hcard0 : Nat.card X ≠ 0 := by
    rw [hcard]; exact NeZero.ne N
  obtain ⟨⟨x₀⟩, -⟩ := Nat.card_ne_zero.mp hcard0
  -- The basepoint admits no period shorter than `N`: otherwise the orbit
  -- of `x₀`, which covers all of `X` by transitivity, would have fewer
  -- than `N` elements.
  have hnoshort : ∀ p : Nat, 0 < p → p < N → f^[p] x₀ ≠ x₀ := by
    intro p hp hpN hper
    have hmul : ∀ q : Nat, f^[p * q] x₀ = x₀ := by
      intro q
      rw [Function.iterate_mul]
      exact Function.iterate_fixed hper q
    have hmod : ∀ k : Nat, f^[k] x₀ = f^[k % p] x₀ := by
      intro k
      conv_lhs => rw [← Nat.mod_add_div k p]
      rw [Function.iterate_add_apply, hmul]
    have hsurj : Function.Surjective
        (fun i : Fin p => f^[(i : Nat)] x₀) := by
      intro y
      obtain ⟨n, hn⟩ := hf.2 x₀ y
      exact ⟨⟨n % p, Nat.mod_lt n hp⟩, (hmod n).symm.trans hn⟩
    have hle : Nat.card X ≤ Nat.card (Fin p) :=
      Nat.card_le_card_of_surjective _ hsurj
    have hfin : Nat.card (Fin p) = p :=
      Nat.card_eq_fintype_card.trans (Fintype.card_fin p)
    omega
  -- The orbit enumeration `ZMod N → X` is injective …
  have horb_inj :
      Function.Injective (fun k : ZMod N => f^[k.val] x₀) := by
    have key : ∀ i j : ZMod N,
        f^[i.val] x₀ = f^[j.val] x₀ → i.val ≤ j.val → i = j := by
      intro i j hij hle
      have hper : f^[j.val - i.val] x₀ = x₀ :=
        iterate_sub_fixed f hf.1.1 x₀ hle hij.symm
      have hlt : j.val - i.val < N :=
        lt_of_le_of_lt (Nat.sub_le _ _) (ZMod.val_lt j)
      have hzero : j.val - i.val = 0 := by
        by_contra hne
        exact hnoshort _ (Nat.pos_of_ne_zero hne) hlt hper
      have hval : i.val = j.val := by omega
      calc
        i = ((i.val : Nat) : ZMod N) := (ZMod.natCast_zmod_val i).symm
        _ = ((j.val : Nat) : ZMod N) := by rw [hval]
        _ = j := ZMod.natCast_zmod_val j
    intro i j hij
    rcases le_total i.val j.val with hle | hle
    · exact key i j hij hle
    · exact (key j i hij.symm hle).symm
  -- … hence bijective, by the cardinality bookkeeping.
  have horb_bij :
      Function.Bijective (fun k : ZMod N => f^[k.val] x₀) := by
    rw [Nat.bijective_iff_injective_and_card]
    exact ⟨horb_inj, by rw [Nat.card_zmod, hcard]⟩
  -- Full period `N`: the `N`-th iterate is some orbit point, and a
  -- nonzero landing index would yield a short period.
  have hperiod : f^[N] x₀ = x₀ := by
    obtain ⟨i, hi⟩ := horb_bij.2 (f^[N] x₀)
    have hile : i.val ≤ N := le_of_lt (ZMod.val_lt i)
    have hper : f^[N - i.val] x₀ = x₀ :=
      iterate_sub_fixed f hf.1.1 x₀ hile hi.symm
    by_cases h0 : i.val = 0
    · simpa [h0] using hper
    · have hilt : i.val < N := ZMod.val_lt i
      exact absurd hper (hnoshort _ (by omega) (by omega))
  have hmulN : ∀ q : Nat, f^[N * q] x₀ = x₀ := by
    intro q
    rw [Function.iterate_mul]
    exact Function.iterate_fixed hperiod q
  -- Orbit points indexed by natural-number casts.
  have horb_natCast : ∀ n : Nat,
      f^[((n : Nat) : ZMod N).val] x₀ = f^[n] x₀ := by
    intro n
    rw [ZMod.val_natCast]
    conv_rhs => rw [← Nat.mod_add_div n N]
    rw [Function.iterate_add_apply, hmulN]
  -- The orbit enumeration steps by one (the wrap case `k.val = N - 1`
  -- is absorbed by the cast computation through `hperiod`).
  have horb_step : ∀ k : ZMod N,
      f^[(k + 1).val] x₀ = f (f^[k.val] x₀) := by
    intro k
    have hk : ((k.val : Nat) : ZMod N) = k := ZMod.natCast_zmod_val k
    have hcast : k + 1 = (((k.val + 1 : Nat)) : ZMod N) := by
      rw [Nat.cast_add, Nat.cast_one, hk]
    calc
      f^[(k + 1).val] x₀
          = f^[(((k.val + 1 : Nat)) : ZMod N).val] x₀ := by rw [hcast]
      _ = f^[k.val + 1] x₀ := horb_natCast (k.val + 1)
      _ = f (f^[k.val] x₀) := Function.iterate_succ_apply' f k.val x₀
  refine ⟨(Equiv.ofBijective _ horb_bij).symm, fun x => ?_⟩
  rw [Equiv.symm_apply_eq]
  calc
    f x = f ((Equiv.ofBijective _ horb_bij)
          ((Equiv.ofBijective _ horb_bij).symm x)) := by
        rw [Equiv.apply_symm_apply]
    _ = (Equiv.ofBijective _ horb_bij)
          ((Equiv.ofBijective _ horb_bij).symm x + 1) :=
        (horb_step ((Equiv.ofBijective _ horb_bij).symm x)).symm

/-- Packaged corollary of `rankEquiv_of_singleCycle` with the modulus
fixed to the cardinality of the carrier. -/
theorem rankEquiv_of_singleCycle_card {X : Type*} [Finite X]
    (f : X → X) (hf : Shared.IsSingleCycleMap f) [NeZero (Nat.card X)] :
    ∃ rank : X ≃ ZMod (Nat.card X), ∀ x, rank (f x) = rank x + 1 :=
  rankEquiv_of_singleCycle f hf rfl

/-! ## Part 2: the tower -/

/-- Iterated skew-product space: `r` coordinates appended to the base. -/
def towerSpace (Base : Type*) (m : Nat) : Nat → Type _
  | 0 => Base
  | r + 1 => towerSpace Base m r × ZMod m

/-- Each tower level is finite when the base is finite and `m ≠ 0`. -/
instance towerSpace_finite {Base : Type*} [Finite Base] {m : Nat}
    [NeZero m] : ∀ r : Nat, Finite (towerSpace Base m r)
  | 0 => inferInstanceAs (Finite Base)
  | r + 1 =>
      haveI := towerSpace_finite (Base := Base) (m := m) r
      inferInstanceAs (Finite (towerSpace Base m r × ZMod m))

/-- Cardinality of the tower space: each appended coordinate multiplies
the count by `m`. -/
theorem card_towerSpace (Base : Type*) [Finite Base] (m : Nat)
    [NeZero m] :
    ∀ r : Nat, Nat.card (towerSpace Base m r) = Nat.card Base * m ^ r
  | 0 => by simp [towerSpace]
  | r + 1 => by
      have ih := card_towerSpace Base m r
      calc
        Nat.card (towerSpace Base m (r + 1))
            = Nat.card (towerSpace Base m r) * Nat.card (ZMod m) :=
          Nat.card_prod _ _
        _ = Nat.card Base * m ^ r * m := by rw [ih, Nat.card_zmod]
        _ = Nat.card Base * m ^ (r + 1) := by ring

/-- The tower space has nonzero cardinality whenever the base does and
`m ≠ 0`. -/
theorem card_towerSpace_ne_zero (Base : Type*) [Finite Base]
    [NeZero (Nat.card Base)] (m : Nat) [NeZero m] (r : Nat) :
    Nat.card (towerSpace Base m r) ≠ 0 := by
  rw [card_towerSpace]
  exact mul_ne_zero (NeZero.ne _) (pow_ne_zero r (NeZero.ne m))

/-- Tower of completion certificates: one per appended coordinate, each
over the skew-product space built so far, with unit crossing increments. -/
structure CompletionTower (Base Coord : Type*) (m : Nat) (r : Nat) where
  /-- The certificate appended at level `k`, over the `k`-level space. -/
  cert : (k : Fin r) →
    CompletionCarryCertificate (towerSpace Base m k.val) Coord m
  /-- Every appended crossing increment is a unit of `ZMod m`. -/
  epsilonUnit : ∀ k : Fin r, IsUnit (cert k).epsilon

/-- Iterated skew map driven by a family of certificates (one per
level); recursion is on the level count with the certificate family
restricted along `Fin.castSucc`. -/
def towerMapAux {Base Coord : Type*} {m : Nat} (S : Base → Base) :
    (r : Nat) →
      ((k : Fin r) →
        CompletionCarryCertificate (towerSpace Base m k.val) Coord m) →
      towerSpace Base m r → towerSpace Base m r
  | 0, _ => S
  | r + 1, cert =>
      additiveSkewMap (towerMapAux S r fun k => cert k.castSucc)
        (completionCarry (cert (Fin.last r)).coordRead
          (cert (Fin.last r)).row (cert (Fin.last r)).tail)

/-- The iterated skew map of a completion tower. -/
def towerMap {Base Coord : Type*} {m r : Nat} (S : Base → Base)
    (T : CompletionTower Base Coord m r) :
    towerSpace Base m r → towerSpace Base m r :=
  towerMapAux S r T.cert

/-- Drop the last certificate of a tower. -/
def CompletionTower.restrict {Base Coord : Type*} {m r : Nat}
    (T : CompletionTower Base Coord m (r + 1)) :
    CompletionTower Base Coord m r where
  cert k := T.cert k.castSucc
  epsilonUnit k := T.epsilonUnit k.castSucc

/-- `towerMap` at level `r + 1` is one completion-carry skew step over
the restricted tower (definitional). -/
theorem towerMap_succ {Base Coord : Type*} {m r : Nat} (S : Base → Base)
    (T : CompletionTower Base Coord m (r + 1)) :
    towerMap S T =
      additiveSkewMap (towerMap S T.restrict)
        (completionCarry (T.cert (Fin.last r)).coordRead
          (T.cert (Fin.last r)).row (T.cert (Fin.last r)).tail) :=
  rfl

/-- Tower induction: a single-cycle base step lifts through every level
of a certificate family with unit crossing increments. -/
theorem towerMapAux_singleCycle {Base Coord : Type*} [Finite Base]
    {m : Nat} [NeZero m] [NeZero (Nat.card Base)]
    (S : Base → Base) (hS : Shared.IsSingleCycleMap S) :
    ∀ (r : Nat)
      (cert : (k : Fin r) →
        CompletionCarryCertificate (towerSpace Base m k.val) Coord m),
      (∀ k, IsUnit (cert k).epsilon) →
      Shared.IsSingleCycleMap (towerMapAux S r cert)
  | 0, _, _ => hS
  | r + 1, cert, hunit => by
      have ih := towerMapAux_singleCycle S hS r
        (fun k => cert k.castSucc) (fun k => hunit k.castSucc)
      have hcard0 : Nat.card (towerSpace Base m r) ≠ 0 :=
        card_towerSpace_ne_zero Base m r
      haveI : NeZero (Nat.card (towerSpace Base m r)) := ⟨hcard0⟩
      obtain ⟨pt⟩ : Nonempty (towerSpace Base m r) :=
        (Nat.card_ne_zero.mp hcard0).1
      obtain ⟨rank, hrank⟩ := rankEquiv_of_singleCycle
        (towerMapAux S r fun k => cert k.castSucc) ih rfl
      exact completionCarryCertificate_singleCycle
        (towerMapAux S r fun k => cert k.castSucc) rank pt
        (cert (Fin.last r)) hrank (hunit (Fin.last r))

/-- Main theorem: the iterated skew map of a completion tower over a
single-cycle base step is itself a single cycle. -/
theorem towerMap_singleCycle {Base Coord : Type*} [Finite Base]
    {m r : Nat} [NeZero m] (S : Base → Base)
    (T : CompletionTower Base Coord m r)
    (hS : Shared.IsSingleCycleMap S) [NeZero (Nat.card Base)] :
    Shared.IsSingleCycleMap (towerMap S T) :=
  towerMapAux_singleCycle S hS r T.cert T.epsilonUnit

/-! ## Part 3: sanity instance over the existing `b = 4` certificate -/

/-- The unique certificate slot of a length-one tower (the level-`0`
space is definitionally the base). -/
def singleSlot {Base Coord : Type*} {m : Nat}
    (C : CompletionCarryCertificate Base Coord m) :
    (n : Nat) → n < 1 →
      CompletionCarryCertificate (towerSpace Base m n) Coord m
  | 0, _ => C
  | n + 1, h => absurd h (by omega)

/-- The single slot carries the certificate's crossing increment. -/
theorem singleSlot_epsilon {Base Coord : Type*} {m : Nat}
    (C : CompletionCarryCertificate Base Coord m) :
    ∀ (n : Nat) (h : n < 1), (singleSlot C n h).epsilon = C.epsilon
  | 0, _ => rfl
  | n + 1, h => absurd h (by omega)

/-- A length-one tower from a single certificate over the base. -/
def CompletionTower.single {Base Coord : Type*} {m : Nat}
    (C : CompletionCarryCertificate Base Coord m)
    (hC : IsUnit C.epsilon) :
    CompletionTower Base Coord m 1 where
  cert k := singleSlot C k.val k.isLt
  epsilonUnit k := by
    rw [singleSlot_epsilon]
    exact hC

/-- The `Fin N` rotation used as base step by the `Fin`-style completion
certificates is a single cycle. -/
theorem finCompletionBaseStep_singleCycle (N : Nat) [NeZero N] :
    Shared.IsSingleCycleMap
      (EndpointCompletion.finCompletionBaseStep (N := N)) :=
  Shared.single_cycle_of_zmod_rank_equiv _ (ZMod.finEquiv N).toEquiv
    EndpointCompletion.finCompletionBaseStep_rank

/-- The crossing increment of the `b = 4` first-completion one-point
certificate is the unit `1`. -/
theorem endpointB4FirstCompletionOnePointCertificate_epsilonUnit
    (m : Nat) :
    IsUnit ((EndpointCompletion.endpointB4FirstCompletionOnePointCertificate
      m).toCompletionCarryCertificate).epsilon :=
  isUnit_one

/-- Length-one completion tower packaging the existing `b = 4`
first-completion one-point certificate over the `Fin 1` base. -/
def endpointB4FirstCompletionTower (m : Nat) :
    CompletionTower (Fin 1) (ZMod 9) m 1 :=
  CompletionTower.single
    (EndpointCompletion.endpointB4FirstCompletionOnePointCertificate
      m).toCompletionCarryCertificate
    (endpointB4FirstCompletionOnePointCertificate_epsilonUnit m)

/-- Sanity check: one tower step over the `b = 4` first-completion
certificate is a single cycle, via `towerMap_singleCycle`. -/
theorem endpointB4FirstCompletionTower_singleCycle (m : Nat) [NeZero m] :
    Shared.IsSingleCycleMap
      (towerMap (EndpointCompletion.finCompletionBaseStep (N := 1))
        (endpointB4FirstCompletionTower m)) :=
  haveI : NeZero (Nat.card (Fin 1)) :=
    ⟨by simp [Nat.card_eq_fintype_card]⟩
  towerMap_singleCycle _ _ (finCompletionBaseStep_singleCycle 1)

end CompletionTower
end V28Hard
end EvenV11
