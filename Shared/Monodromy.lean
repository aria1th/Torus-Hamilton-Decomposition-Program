import Shared.RankCycle

namespace Shared

def skewProductMap {Base Fiber : Type*}
    (baseStep : Base → Base) (fiberStep : Base → Fiber → Fiber) :
    Base × Fiber → Base × Fiber :=
  fun x => (baseStep x.1, fiberStep x.1 x.2)

def skewFiberIterate {Base Fiber : Type*}
    (baseStep : Base → Base) (fiberStep : Base → Fiber → Fiber) :
    Nat → Base → Fiber → Fiber
  | 0, _base, fiber => fiber
  | n + 1, base, fiber =>
      skewFiberIterate baseStep fiberStep n
        (baseStep base) (fiberStep base fiber)

theorem skewProductMap_iterate_eq_base_fiber {Base Fiber : Type*}
    (baseStep : Base → Base) (fiberStep : Base → Fiber → Fiber) :
    ∀ n : Nat, ∀ x : Base × Fiber,
      (skewProductMap baseStep fiberStep)^[n] x =
        ((baseStep^[n]) x.1,
          skewFiberIterate baseStep fiberStep n x.1 x.2)
  | 0, x => by simp [skewFiberIterate]
  | n + 1, x => by
      rw [Function.iterate_succ_apply]
      rw [skewProductMap_iterate_eq_base_fiber baseStep fiberStep n
        (skewProductMap baseStep fiberStep x)]
      simp [skewProductMap, skewFiberIterate, Function.iterate_succ_apply]

theorem skewProductMap_snd_iterate {Base Fiber : Type*}
    (baseStep : Base → Base) (fiberStep : Base → Fiber → Fiber)
    (n : Nat) (x : Base × Fiber) :
    ((skewProductMap baseStep fiberStep)^[n] x).2 =
      skewFiberIterate baseStep fiberStep n x.1 x.2 := by
  rw [skewProductMap_iterate_eq_base_fiber]

theorem skewFiberIterate_bijective {Base Fiber : Type*}
    (baseStep : Base → Base) (fiberStep : Base → Fiber → Fiber)
    (hfiber : ∀ base : Base, Function.Bijective (fiberStep base)) :
    ∀ n : Nat, ∀ base : Base,
      Function.Bijective (skewFiberIterate baseStep fiberStep n base)
  | 0, _base => by
      constructor
      · intro x y hxy
        exact hxy
      · intro y
        exact ⟨y, rfl⟩
  | n + 1, base => by
      have htail :=
        skewFiberIterate_bijective baseStep fiberStep hfiber n
          (baseStep base)
      constructor
      · intro x y hxy
        apply (hfiber base).1
        apply htail.1
        simpa [skewFiberIterate] using hxy
      · intro y
        rcases htail.2 y with ⟨u, hu⟩
        rcases (hfiber base).2 u with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        simp [skewFiberIterate, hx, hu]

theorem skewProductMap_fst_iterate {Base Fiber : Type*}
    (baseStep : Base → Base) (fiberStep : Base → Fiber → Fiber) :
    ∀ n : Nat, ∀ x : Base × Fiber,
      ((skewProductMap baseStep fiberStep)^[n] x).1 =
        (baseStep^[n]) x.1 := by
  intro n
  induction n with
  | zero =>
      intro x
      simp
  | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      simp [skewProductMap, ih, Function.iterate_succ_apply']

theorem skewProductMap_bijective {Base Fiber : Type*}
    (baseStep : Base → Base) (fiberStep : Base → Fiber → Fiber)
    (hbase : Function.Bijective baseStep)
    (hfiber : ∀ u : Base, Function.Bijective (fiberStep u)) :
    Function.Bijective (skewProductMap baseStep fiberStep) := by
  constructor
  · intro x y hxy
    rcases x with ⟨ux, vx⟩
    rcases y with ⟨uy, vy⟩
    have hu : ux = uy := hbase.1 (congrArg Prod.fst hxy)
    subst uy
    have hv : vx = vy := (hfiber ux).1 (congrArg Prod.snd hxy)
    exact Prod.ext rfl hv
  · intro y
    rcases y with ⟨u', v'⟩
    rcases hbase.2 u' with ⟨u, hu⟩
    rcases (hfiber u).2 v' with ⟨v, hv⟩
    exact ⟨(u, v), Prod.ext hu hv⟩

theorem skewProductMap_fiber_bijective_of_bijective {Base Fiber : Type*}
    (baseStep : Base → Base) (fiberStep : Base → Fiber → Fiber)
    (hS : Function.Bijective (skewProductMap baseStep fiberStep))
    (hbase : Function.Bijective baseStep) :
    ∀ u : Base, Function.Bijective (fiberStep u) := by
  intro u
  constructor
  · intro x y hxy
    have hprod :
        skewProductMap baseStep fiberStep (u, x) =
          skewProductMap baseStep fiberStep (u, y) := by
      exact Prod.ext rfl hxy
    exact congrArg Prod.snd (hS.1 hprod)
  · intro y
    rcases hS.2 (baseStep u, y) with ⟨ux, hux⟩
    rcases ux with ⟨u', x⟩
    have hu : u' = u := by
      exact hbase.1 (congrArg Prod.fst hux)
    subst u'
    exact ⟨x, congrArg Prod.snd hux⟩

theorem bijective_of_equiv_conj {α β : Type*} (e : α ≃ β)
    (f : β → β) (g : α → α)
    (hg : Function.Bijective g)
    (hconj : ∀ x : α, e.symm (f (e x)) = g x) :
    Function.Bijective f := by
  constructor
  · intro y1 y2 hy
    apply e.symm.injective
    apply hg.1
    calc
      g (e.symm y1) = e.symm (f (e (e.symm y1))) := by
        rw [hconj]
      _ = e.symm (f y1) := by simp
      _ = e.symm (f y2) := by rw [hy]
      _ = e.symm (f (e (e.symm y2))) := by simp
      _ = g (e.symm y2) := by rw [hconj]
  · intro y
    rcases hg.2 (e.symm y) with ⟨x, hx⟩
    refine ⟨e x, ?_⟩
    apply e.symm.injective
    calc
      e.symm (f (e x)) = g x := hconj x
      _ = e.symm y := hx

theorem single_cycle_of_equiv_conj {α β : Type*} (e : α ≃ β)
    (f : β → β) (g : α → α)
    (hg : IsSingleCycleMap g)
    (hconj : ∀ x : α, e.symm (f (e x)) = g x) :
    IsSingleCycleMap f := by
  have hiter :
      ∀ n : Nat, ∀ x : α,
        e.symm ((f^[n]) (e x)) = (g^[n]) x := by
    intro n
    induction n with
    | zero =>
        intro x
        simp
    | succ n ih =>
        intro x
        rw [Function.iterate_succ_apply']
        have hstep : (f^[n]) (e x) = e ((g^[n]) x) := by
          apply e.symm.injective
          simpa using ih x
        rw [hstep]
        simpa [Function.iterate_succ_apply'] using hconj ((g^[n]) x)
  refine ⟨bijective_of_equiv_conj e f g hg.1 hconj, ?_⟩
  intro y1 y2
  rcases hg.2 (e.symm y1) (e.symm y2) with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  apply e.symm.injective
  calc
    e.symm ((f^[n]) y1) =
        e.symm ((f^[n]) (e (e.symm y1))) := by simp
    _ = (g^[n]) (e.symm y1) := hiter n (e.symm y1)
    _ = e.symm y2 := hn

def sectionReturn {Base Fiber : Type*}
    (S : Base × Fiber → Base × Fiber) (base : Base) (period : Nat) :
    Fiber → Fiber :=
  fun v => (S^[period] (base, v)).2

theorem sectionReturn_skewProductMap_eq_fiberIterate {Base Fiber : Type*}
    (baseStep : Base → Base) (fiberStep : Base → Fiber → Fiber)
    (base : Base) (period : Nat) :
    sectionReturn (skewProductMap baseStep fiberStep) base period =
      skewFiberIterate baseStep fiberStep period base := by
  funext fiber
  unfold sectionReturn
  rw [skewProductMap_snd_iterate]

theorem sectionReturn_skewProductMap_bijective {Base Fiber : Type*}
    (baseStep : Base → Base) (fiberStep : Base → Fiber → Fiber)
    (base : Base) (period : Nat)
    (hfiber : ∀ base : Base, Function.Bijective (fiberStep base)) :
    Function.Bijective
      (sectionReturn (skewProductMap baseStep fiberStep) base period) := by
  rw [sectionReturn_skewProductMap_eq_fiberIterate]
  exact skewFiberIterate_bijective baseStep fiberStep hfiber period base

def skewFiberAdditiveCarry {Base : Type*} {m : Nat}
    (baseStep : Base → Base) (carry : Base → ZMod m) :
    Nat → Base → ZMod m
  | 0, _base => 0
  | n + 1, base =>
      carry base + skewFiberAdditiveCarry baseStep carry n (baseStep base)

theorem skewFiberIterate_zmod_add {Base : Type*} {m : Nat}
    (baseStep : Base → Base) (carry : Base → ZMod m) :
    ∀ n : Nat, ∀ base : Base, ∀ fiber : ZMod m,
      skewFiberIterate baseStep (fun b z => z + carry b) n base fiber =
        fiber + skewFiberAdditiveCarry baseStep carry n base
  | 0, _base, _fiber => by simp [skewFiberIterate, skewFiberAdditiveCarry]
  | n + 1, base, fiber => by
      rw [skewFiberIterate, skewFiberIterate_zmod_add baseStep carry n]
      simp [skewFiberAdditiveCarry]
      ring

theorem sectionReturn_skewProductMap_zmod_add {Base : Type*} {m : Nat}
    (baseStep : Base → Base) (carry : Base → ZMod m)
    (base : Base) (period : Nat) :
    sectionReturn (skewProductMap baseStep (fun b z => z + carry b))
        base period =
      fun fiber : ZMod m =>
        fiber + skewFiberAdditiveCarry baseStep carry period base := by
  funext fiber
  unfold sectionReturn
  rw [skewProductMap_snd_iterate]
  rw [skewFiberIterate_zmod_add]

theorem sectionReturn_skewProductMap_zmod_add_single_cycle_of_coprime
    {Base : Type*} {m : Nat} [NeZero m]
    (baseStep : Base → Base) (carry : Base → ZMod m)
    (base : Base) (period a : Nat)
    (ha : Nat.Coprime a m)
    (hcarry :
      skewFiberAdditiveCarry baseStep carry period base = (a : ZMod m)) :
    IsSingleCycleMap
      (sectionReturn
        (skewProductMap baseStep (fun b z => z + carry b))
        base period) := by
  rw [sectionReturn_skewProductMap_zmod_add]
  rw [hcarry]
  exact zmod_add_single_cycle_of_coprime ha

theorem zmod_add_const_bijective {m : Nat} (a : ZMod m) :
    Function.Bijective (fun z : ZMod m => z + a) := by
  constructor
  · intro x y hxy
    exact add_right_cancel hxy
  · intro y
    refine ⟨y - a, ?_⟩
    simp

theorem single_cycle_of_skewProduct_monodromy
    {Base Fiber : Type*} (S : Base × Fiber → Base × Fiber)
    (base : Base) (period : Nat)
    (hS : Function.Bijective S)
    (hreturnBase : ∀ v : Fiber, (S^[period] (base, v)).1 = base)
    (hmonodromy : IsSingleCycleMap (sectionReturn S base period))
    (hcover : ∀ x : Base × Fiber, ∃ v : Fiber, ∃ k : Nat,
      k < period ∧ S^[k] (base, v) = x) :
    IsSingleCycleMap S := by
  have hreturn :
      ∀ v : Fiber,
        S^[period] (base, v) =
          (base, sectionReturn S base period v) := by
    intro v
    exact Prod.ext (hreturnBase v) rfl
  exact single_cycle_of_periodic_return_cover
    (S := S) (base := fun v : Fiber => (base, v))
    (R := sectionReturn S base period) (period := period)
    hS hreturn hmonodromy hcover

theorem single_cycle_of_skewProduct_base_orbit_monodromy
    {Base Fiber : Type*}
    (baseStep : Base → Base) (fiberStep : Base → Fiber → Fiber)
    (base : Base) (period : Nat)
    (hbase : Function.Bijective baseStep)
    (hfiber : ∀ u : Base, Function.Bijective (fiberStep u))
    (hreturnBase : (baseStep^[period]) base = base)
    (hbaseCover : ∀ b : Base, ∃ k : Nat,
      k < period ∧ (baseStep^[k]) base = b)
    (hmonodromy :
      IsSingleCycleMap
        (sectionReturn (skewProductMap baseStep fiberStep) base period)) :
    IsSingleCycleMap (skewProductMap baseStep fiberStep) := by
  let S : Base × Fiber → Base × Fiber :=
    skewProductMap baseStep fiberStep
  have hS : Function.Bijective S :=
    skewProductMap_bijective baseStep fiberStep hbase hfiber
  have hreturn : ∀ v : Fiber, (S^[period] (base, v)).1 = base := by
    intro v
    calc
      (S^[period] (base, v)).1 = (baseStep^[period]) base := by
        simpa [S] using
          skewProductMap_fst_iterate baseStep fiberStep period (base, v)
      _ = base := hreturnBase
  have hcover : ∀ x : Base × Fiber, ∃ v : Fiber, ∃ k : Nat,
      k < period ∧ S^[k] (base, v) = x := by
    intro x
    rcases x with ⟨b, v⟩
    rcases hbaseCover b with ⟨k, hklt, hk⟩
    rcases (Function.Bijective.iterate hS k).2 (b, v) with ⟨y, hy⟩
    rcases y with ⟨yb, yf⟩
    have hyb : yb = base := by
      apply (Function.Bijective.iterate hbase k).1
      calc
        (baseStep^[k]) yb = (S^[k] (yb, yf)).1 := by
          simpa [S] using
            (skewProductMap_fst_iterate baseStep fiberStep k (yb, yf)).symm
        _ = b := by
          rw [hy]
        _ = (baseStep^[k]) base := hk.symm
    subst yb
    exact ⟨yf, k, hklt, hy⟩
  exact single_cycle_of_skewProduct_monodromy
    (S := S) (base := base) (period := period)
    hS hreturn (by simpa [S] using hmonodromy) hcover

theorem single_cycle_of_skewProduct_zmod_additive_carry
    {Base : Type*} {m : Nat} [NeZero m]
    (baseStep : Base → Base) (carry : Base → ZMod m)
    (base : Base) (period a : Nat)
    (hbase : Function.Bijective baseStep)
    (hreturnBase : (baseStep^[period]) base = base)
    (hbaseCover : ∀ b : Base, ∃ k : Nat,
      k < period ∧ (baseStep^[k]) base = b)
    (ha : Nat.Coprime a m)
    (hcarry :
      skewFiberAdditiveCarry baseStep carry period base = (a : ZMod m)) :
    IsSingleCycleMap
      (skewProductMap baseStep (fun b z => z + carry b)) :=
  single_cycle_of_skewProduct_base_orbit_monodromy
    baseStep (fun b z => z + carry b) base period
    hbase
    (fun b => zmod_add_const_bijective (carry b))
    hreturnBase hbaseCover
    (sectionReturn_skewProductMap_zmod_add_single_cycle_of_coprime
      baseStep carry base period a ha hcarry)

end Shared
