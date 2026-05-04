import Mathlib.GroupTheory.Perm.Cycle.Basic
import Shared.RankCycle

namespace Shared

abbrev TorusVertex (d m : Nat) := Fin d → ZMod m

abbrev TorusDirection (d : Nat) := Fin d

abbrev TorusColor (d : Nat) := Fin d

def torusBasis (d m : Nat) (i : TorusDirection d) : TorusVertex d m :=
  fun j => if j = i then 1 else 0

def blockIndexEquiv (a b : Nat) : Fin b × Fin a ≃ Fin (a * b) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm b a))

def torusVertexBlockEquiv (a b m : Nat) :
    TorusVertex (a * b) m ≃ (Fin b → TorusVertex a m) where
  toFun x := fun j i => x (blockIndexEquiv a b (j, i))
  invFun y := fun k =>
    y ((blockIndexEquiv a b).symm k).1 ((blockIndexEquiv a b).symm k).2
  left_inv := by
    intro x
    funext k
    simp
  right_inv := by
    intro y
    funext j i
    simp

theorem torusVertexBlockEquiv_apply
    {a b m : Nat} (x : TorusVertex (a * b) m)
    (j : Fin b) (i : Fin a) :
    torusVertexBlockEquiv a b m x j i =
      x (blockIndexEquiv a b (j, i)) := by
  rfl

theorem torusVertexBlockEquiv_symm_apply
    {a b m : Nat} (y : Fin b → TorusVertex a m)
    (k : Fin (a * b)) :
    (torusVertexBlockEquiv a b m).symm y k =
      y ((blockIndexEquiv a b).symm k).1
        ((blockIndexEquiv a b).symm k).2 := by
  rfl

theorem card_torusVertex (d m : Nat) [NeZero m] :
    Fintype.card (TorusVertex d m) = m ^ d := by
  calc
    Fintype.card (TorusVertex d m) = Fintype.card (ZMod m) ^ d := by
      simp [TorusVertex]
    _ = m ^ d := by
      rw [ZMod.card m]

theorem card_zmodVector (n m : Nat) [NeZero m] :
    Fintype.card (Fin n → ZMod m) = m ^ n := by
  exact card_torusVertex n m

noncomputable def zmodVectorPowerEquiv (n m : Nat) [NeZero m] :
    (Fin n → ZMod m) ≃ ZMod (m ^ n) :=
  Fintype.equivOfCardEq (by
    rw [card_zmodVector n m]
    rw [ZMod.card (m ^ n)])

def zmodVectorTake {m r k : Nat} (hk : k ≤ r)
    (x : Fin r → ZMod m) : Fin k → ZMod m :=
  fun i => x ⟨i.val, lt_of_lt_of_le i.isLt hk⟩

def zmodVectorExtendZero {m k r : Nat} (_hk : k ≤ r)
    (x : Fin k → ZMod m) : Fin r → ZMod m :=
  fun i => if h : i.val < k then x ⟨i.val, h⟩ else 0

def zmodVectorSnocEquiv (n m : Nat) :
    (Fin (n + 1) → ZMod m) ≃ (Fin n → ZMod m) × ZMod m :=
  (Fin.snocEquiv (fun _ : Fin (n + 1) => ZMod m)).symm.trans
    (Equiv.prodComm _ _)

@[simp] theorem zmodVectorSnocEquiv_apply {n m : Nat}
    (x : Fin (n + 1) → ZMod m) :
    zmodVectorSnocEquiv n m x = (Fin.init x, x (Fin.last n)) := by
  rfl

@[simp] theorem zmodVectorSnocEquiv_symm_apply {n m : Nat}
    (x : Fin n → ZMod m) (a : ZMod m) :
    (zmodVectorSnocEquiv n m).symm (x, a) = Fin.snoc x a := by
  rfl

@[simp] theorem zmodVectorTake_snoc_self {m n : Nat}
    (x : Fin n → ZMod m) (a : ZMod m) :
    zmodVectorTake (m := m) (r := n + 1) (k := n)
      (Nat.le_succ n) (Fin.snoc x a) = x := by
  funext i
  change @Fin.snoc n (fun _ => ZMod m) x a i.castSucc = x i
  exact Fin.snoc_castSucc (α := fun _ : Fin (n + 1) => ZMod m) a x i

@[simp] theorem zmodVectorTake_snoc {m n k : Nat} (hk : k ≤ n)
    (x : Fin n → ZMod m) (a : ZMod m) :
    zmodVectorTake (m := m) (r := n + 1) (k := k)
      (Nat.le_trans hk (Nat.le_succ n)) (Fin.snoc x a) =
        zmodVectorTake (m := m) (r := n) (k := k) hk x := by
  funext i
  let j : Fin n := ⟨i.val, lt_of_lt_of_le i.isLt hk⟩
  have hidx :
      (⟨i.val, lt_of_lt_of_le i.isLt
        (Nat.le_trans hk (Nat.le_succ n))⟩ : Fin (n + 1)) =
        j.castSucc := rfl
  change @Fin.snoc n (fun _ => ZMod m) x a
      (⟨i.val, lt_of_lt_of_le i.isLt
        (Nat.le_trans hk (Nat.le_succ n))⟩ : Fin (n + 1)) = x j
  rw [hidx]
  exact Fin.snoc_castSucc (α := fun _ : Fin (n + 1) => ZMod m) a x j

theorem torusVertexBlockEquiv_torusBasis_apply
    {a b m : Nat} (j j' : Fin b) (i i' : Fin a) :
    torusVertexBlockEquiv a b m
        (torusBasis (a * b) m (blockIndexEquiv a b (j, i))) j' i' =
      if j' = j ∧ i' = i then 1 else 0 := by
  by_cases h : j' = j ∧ i' = i
  · rcases h with ⟨rfl, rfl⟩
    simp [torusVertexBlockEquiv_apply, torusBasis]
  · have hne : blockIndexEquiv a b (j', i') ≠ blockIndexEquiv a b (j, i) := by
      intro heq
      exact h <| Prod.ext_iff.1 ((blockIndexEquiv a b).injective heq)
    simp [torusVertexBlockEquiv_apply, torusBasis, h, hne]

theorem torusVertexBlockEquiv_add_torusBasis_apply
    {a b m : Nat} (x : TorusVertex (a * b) m)
    (j q : Fin b) (i : Fin a) :
    torusVertexBlockEquiv a b m
        (x + torusBasis (a * b) m (blockIndexEquiv a b (j, i))) q =
      torusVertexBlockEquiv a b m x q +
        if q = j then torusBasis a m i else 0 := by
  funext r
  by_cases hq : q = j
  · subst q
    by_cases hr : r = i
    · subst hr
      simp [torusVertexBlockEquiv_apply, torusBasis]
    · have hne :
          blockIndexEquiv a b (j, r) ≠ blockIndexEquiv a b (j, i) := by
        intro heq
        exact hr <| congrArg Prod.snd ((blockIndexEquiv a b).injective heq)
      simp [torusVertexBlockEquiv_apply, torusBasis, hr, hne]
  · have hne :
        blockIndexEquiv a b (q, r) ≠ blockIndexEquiv a b (j, i) := by
      intro heq
      exact hq <| congrArg Prod.fst ((blockIndexEquiv a b).injective heq)
    simp [torusVertexBlockEquiv_apply, torusBasis, hq, hne]

structure CycleCoordinate (n : Nat) [NeZero n]
    {α : Type*} (f : α → α) where
  equiv : ZMod n ≃ α
  step : ∀ z : ZMod n, equiv (z + 1) = f (equiv z)

/--
Generic lower-triangular odometer theorem for `ZMod m` vector spaces.  A map
whose `k`-th coordinate is `x_k + gamma_k(x_0,...,x_{k-1})` is a single cycle
when every total carry `sum gamma_k` is a unit.  The target is stated as a
rank-equivalence witness so this remains a `Prop`; callers can convert it to
`CycleCoordinate` with `CycleCoordinate.ofRankEquiv`.
-/
def ZModVectorLowerTriangularUnitCycleCoordinateGoal : Prop :=
  ∀ {m r : Nat} [NeZero m],
    ∀ (F : (Fin r → ZMod m) → (Fin r → ZMod m))
      (gamma : ∀ k : Nat, k < r → (Fin k → ZMod m) → ZMod m),
      (∀ x : Fin r → ZMod m, ∀ k : Nat, ∀ hk : k < r,
        F x ⟨k, hk⟩ =
          x ⟨k, hk⟩ +
            gamma k hk (zmodVectorTake (Nat.le_of_lt hk) x)) →
      (∀ k : Nat, ∀ hk : k < r,
        IsUnit (∑ x : (Fin k → ZMod m), gamma k hk x)) →
      ∃ e : ((Fin r → ZMod m) ≃ ZMod (m ^ r)),
        ∀ x : Fin r → ZMod m, e (F x) = e x + 1

namespace CycleCoordinate

noncomputable def ofRankEquiv {n : Nat} [NeZero n] {α : Type*} {f : α → α}
    (rank : α ≃ ZMod n)
    (hstep : ∀ x : α, rank (f x) = rank x + 1) :
    CycleCoordinate n f where
  equiv := rank.symm
  step := by
    intro z
    apply rank.injective
    calc
      rank (rank.symm (z + 1)) = z + 1 := by simp
      _ = rank (rank.symm z) + 1 := by simp
      _ = rank (f (rank.symm z)) := by rw [hstep]

noncomputable def ofRank {n : Nat} [NeZero n] {α : Type*} {f : α → α}
    (rank : α → ZMod n)
    (hrank : Function.Bijective rank)
    (hstep : ∀ x : α, rank (f x) = rank x + 1) :
    CycleCoordinate n f :=
  ofRankEquiv (Equiv.ofBijective rank hrank) hstep

noncomputable def ofFinRank {n : Nat} [NeZero n] {α : Type*} {f : α → α}
    (rank : α → Fin n)
    (hrank : Function.Bijective rank)
    (hstep : ∀ x : α,
      (ZMod.finEquiv n) (rank (f x)) = (ZMod.finEquiv n) (rank x) + 1) :
    CycleCoordinate n f :=
  ofRank (fun x => (ZMod.finEquiv n) (rank x))
    ((ZMod.finEquiv n).bijective.comp hrank)
    hstep

theorem finAddOne_zmod {n : Nat} [NeZero n] (i : Fin n) :
    (ZMod.finEquiv n) (i + 1) = (ZMod.finEquiv n) i + 1 := by
  simp only [map_add, map_one]

noncomputable def ofFinEquiv {n : Nat} [NeZero n] {α : Type*} {f : α → α}
    (e : Fin n ≃ α)
    (hstep : ∀ i : Fin n, e (i + 1) = f (e i)) :
    CycleCoordinate n f :=
  ofFinRank e.symm e.symm.bijective (by
    intro x
    let i : Fin n := e.symm x
    have hx : x = e i := by simp [i]
    have hfi : f x = e (i + 1) := by
      rw [hx]
      exact (hstep i).symm
    calc
      (ZMod.finEquiv n) (e.symm (f x)) =
          (ZMod.finEquiv n) (i + 1) := by
        rw [hfi]
        simp [i]
      _ = (ZMod.finEquiv n) i + 1 := finAddOne_zmod i
      _ = (ZMod.finEquiv n) (e.symm x) + 1 := by simp [i])

noncomputable def conj {n : Nat} [NeZero n]
    {α β : Type*} {f : α → α} {g : β → β}
    (C : CycleCoordinate n f) (e : α ≃ β)
    (hcomm : ∀ x : α, e (f x) = g (e x)) :
    CycleCoordinate n g where
  equiv := C.equiv.trans e
  step := by
    intro z
    calc
      (C.equiv.trans e) (z + 1) = e (C.equiv (z + 1)) := rfl
      _ = e (f (C.equiv z)) := by rw [C.step z]
      _ = g (e (C.equiv z)) := hcomm (C.equiv z)
      _ = g ((C.equiv.trans e) z) := rfl

noncomputable def conjOfBijective {n : Nat} [NeZero n]
    {α β : Type*} {f : α → α} {g : β → β}
    (C : CycleCoordinate n f) (phi : α → β)
    (hphi : Function.Bijective phi)
    (hcomm : ∀ x : α, phi (f x) = g (phi x)) :
    CycleCoordinate n g :=
  C.conj (Equiv.ofBijective phi hphi) hcomm

private noncomputable def supportEquivOfEqUniv
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) (h : p.support = Finset.univ) :
    p.support ≃ α where
  toFun x := x.1
  invFun a := ⟨a, by rw [h]; simp⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro a
    rfl

theorem permNoFixed_of_singleCycleMap
    {α : Type*} [Fintype α]
    (f : α → α) (hf : IsSingleCycleMap f)
    (hcard : 1 < Fintype.card α) :
    ∀ x : α, (Equiv.ofBijective f hf.1 : Equiv.Perm α) x ≠ x := by
  classical
  intro x hfix
  rcases Fintype.exists_ne_of_one_lt_card hcard x with ⟨y, hy⟩
  rcases hf.2 x y with ⟨k, hk⟩
  have hiter : ∀ n : Nat, f^[n] x = x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        rw [ih]
        exact hfix
  exact hy (by simpa [hiter k] using hk.symm)

theorem permIsCycle_of_singleCycleMap
    {α : Type*} [Fintype α]
    (f : α → α) (hf : IsSingleCycleMap f)
    (hcard : 1 < Fintype.card α) :
    Equiv.Perm.IsCycle (Equiv.ofBijective f hf.1 : Equiv.Perm α) := by
  classical
  let p : Equiv.Perm α := Equiv.ofBijective f hf.1
  rcases Fintype.exists_pair_of_one_lt_card hcard with ⟨a, _b, _hab⟩
  have hpa : p a ≠ a := permNoFixed_of_singleCycleMap f hf hcard a
  refine ⟨a, hpa, ?_⟩
  intro y _hy
  rcases hf.2 a y with ⟨k, hk⟩
  exact ⟨(k : Int), by simpa [p, zpow_natCast] using hk⟩

theorem permSupport_eq_univ_of_singleCycleMap
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α) (hf : IsSingleCycleMap f)
    (hcard : 1 < Fintype.card α) :
    let p : Equiv.Perm α := Equiv.ofBijective f hf.1
    p.support = Finset.univ := by
  classical
  intro p
  apply Finset.eq_univ_iff_forall.mpr
  intro x
  rw [Equiv.Perm.mem_support]
  exact permNoFixed_of_singleCycleMap f hf hcard x

noncomputable def ofFiniteSingleCycle {n : Nat} [NeZero n]
    {α : Type*} [Fintype α] [DecidableEq α] {f : α → α}
    (hcard : Fintype.card α = n) (hn : 1 < n)
    (hf : IsSingleCycleMap f) :
    CycleCoordinate n f := by
  classical
  let p : Equiv.Perm α := Equiv.ofBijective f hf.1
  have hcardα : 1 < Fintype.card α := by simpa [hcard] using hn
  have hp : p.IsCycle := permIsCycle_of_singleCycleMap f hf hcardα
  have hsupport : p.support = Finset.univ :=
    permSupport_eq_univ_of_singleCycleMap f hf hcardα
  let hfin : IsOfFinOrder p := isOfFinOrder_of_finite p
  have horder : orderOf p = n := by
    calc
      orderOf p = Finset.card p.support := hp.orderOf
      _ = Fintype.card α := by rw [hsupport, Finset.card_univ]
      _ = n := hcard
  let e : Fin n ≃ α :=
    (finCongr horder.symm).trans
      ((finEquivZPowers hfin).trans
        (hp.zpowersEquivSupport.trans (supportEquivOfEqUniv p hsupport)))
  exact ofFinEquiv e (by
    intro i
    dsimp [e]
    haveI : NeZero (orderOf p) :=
      ⟨ne_of_gt (by
        rw [horder]
        exact Nat.pos_of_ne_zero (NeZero.ne n))⟩
    have hcast :
        Fin.cast horder.symm (i + 1) =
          (Fin.cast horder.symm i) + 1 := by
      subst horder
      rfl
    rw [hcast]
    set j : Fin (orderOf p) := Fin.cast horder.symm i
    rw [finEquivZPowers_apply, finEquivZPowers_apply]
    change (p ^ (j + 1).val) (Classical.choose hp) =
      f ((p ^ j.val) (Classical.choose hp))
    have htwo : 2 ≤ orderOf p := by
      rw [hp.orderOf]
      exact hp.two_le_card_support
    have hone : ((1 : Fin (orderOf p)).val) = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt (by omega)
    have hval :
        ((j + 1 : Fin (orderOf p)).val) =
          (j.val + 1) % orderOf p := by
      rw [Fin.val_add, hone]
    rw [hval, pow_mod_orderOf]
    simp [pow_succ', p])

theorem rank_step {n : Nat} [NeZero n] {α : Type*} {f : α → α}
    (C : CycleCoordinate n f) (x : α) :
    C.equiv.symm (f x) = C.equiv.symm x + 1 := by
  let z : ZMod n := C.equiv.symm x
  have hx : x = C.equiv z := by
    simp [z]
  calc
    C.equiv.symm (f x) = C.equiv.symm (f (C.equiv z)) := by rw [hx]
    _ = C.equiv.symm (C.equiv (z + 1)) := by rw [C.step z]
    _ = C.equiv.symm x + 1 := by simp [z]

theorem singleCycle {n : Nat} [NeZero n] {α : Type*} {f : α → α}
    (C : CycleCoordinate n f) :
    IsSingleCycleMap f := by
  refine single_cycle_of_zmod_rank f C.equiv.symm C.equiv.symm.bijective ?_
  intro x
  let z : ZMod n := C.equiv.symm x
  have hx : x = C.equiv z := by
    simp [z]
  calc
    C.equiv.symm (f x) = C.equiv.symm (f (C.equiv z)) := by rw [hx]
    _ = C.equiv.symm (C.equiv (z + 1)) := by rw [C.step z]
    _ = C.equiv.symm x + 1 := by simp [z]

noncomputable def zmodAddConstOfCoprime {m a : Nat} [NeZero m]
    (ha : Nat.Coprime a m) :
    CycleCoordinate m (fun x : ZMod m => x + (a : ZMod m)) := by
  let u : (ZMod m)ˣ := ZMod.unitOfCoprime a ha
  refine ofRank (fun x : ZMod m => (u⁻¹ : ZMod m) * x)
    (Equiv.bijective (Units.mulLeft u⁻¹)) ?_
  intro x
  have hu : (u : ZMod m) = (a : ZMod m) :=
    ZMod.coe_unitOfCoprime a ha
  calc
    (u⁻¹ : ZMod m) * (x + (a : ZMod m)) =
        (u⁻¹ : ZMod m) * x + (u⁻¹ : ZMod m) * (a : ZMod m) := by ring
    _ = (u⁻¹ : ZMod m) * x + (u⁻¹ : ZMod m) * (u : ZMod m) := by rw [hu]
    _ = (u⁻¹ : ZMod m) * x + 1 := by simp

noncomputable def zmodAddConstOfUnit {m : Nat} [NeZero m]
    {a : ZMod m} (ha : IsUnit a) :
    CycleCoordinate m (fun x : ZMod m => x + a) := by
  let u : (ZMod m)ˣ := ha.unit
  refine ofRankEquiv (Units.mulLeft u⁻¹) ?_
  intro x
  have hu : (u : ZMod m) = a := ha.unit_spec
  change (↑(u⁻¹) : ZMod m) * (x + a) =
    (↑(u⁻¹) : ZMod m) * x + 1
  calc
    (↑(u⁻¹) : ZMod m) * (x + a) =
        (↑(u⁻¹) : ZMod m) * x + (↑(u⁻¹) : ZMod m) * a := by ring
    _ = (↑(u⁻¹) : ZMod m) * x + (↑(u⁻¹) : ZMod m) * (u : ZMod m) := by rw [hu]
    _ = (↑(u⁻¹) : ZMod m) * x + 1 := by simp

end CycleCoordinate

def cayleyColorStep {d m : Nat}
    (colorDir : TorusColor d → TorusVertex d m → TorusDirection d)
    (c : TorusColor d) : TorusVertex d m → TorusVertex d m :=
  fun x => x + torusBasis d m (colorDir c x)

def IsCayleyEdgePartition {d m : Nat}
    (colorDir : TorusColor d → TorusVertex d m → TorusDirection d) : Prop :=
  ∀ x : TorusVertex d m, ∀ i : TorusDirection d,
    ∃! c : TorusColor d, colorDir c x = i

def IsCayleyColorHamiltonian {d m : Nat}
    (colorDir : TorusColor d → TorusVertex d m → TorusDirection d) : Prop :=
  ∀ c : TorusColor d, IsSingleCycleMap (cayleyColorStep colorDir c)

structure CayleyDecomposition (d m : Nat) where
  colorDir : TorusColor d → TorusVertex d m → TorusDirection d
  edgePartition : IsCayleyEdgePartition colorDir
  colorHamiltonian : IsCayleyColorHamiltonian colorDir

def CayleyHamiltonDecomposition (d m : Nat) : Prop :=
  Nonempty (CayleyDecomposition d m)

def TorusHamiltonDecomposition (d m : Nat) : Prop :=
  CayleyHamiltonDecomposition d m

theorem torusHamiltonDecomposition_iff_cayley
    {d m : Nat} :
    TorusHamiltonDecomposition d m ↔ CayleyHamiltonDecomposition d m := by
  rfl

end Shared
