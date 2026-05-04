import Shared.TorusCayley

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

def ZModVectorIncrementDependsOnTake {m r : Nat}
    (F : (Fin r → ZMod m) → (Fin r → ZMod m)) : Prop :=
  ∀ x y : Fin r → ZMod m, ∀ k : Nat, ∀ hk : k < r,
    zmodVectorTake (Nat.le_of_lt hk) x =
      zmodVectorTake (Nat.le_of_lt hk) y →
    F x ⟨k, hk⟩ - x ⟨k, hk⟩ =
      F y ⟨k, hk⟩ - y ⟨k, hk⟩

theorem zmodVectorIncrementDependsOnTake_id {m r : Nat} :
    ZModVectorIncrementDependsOnTake
      (fun x : Fin r → ZMod m => x) := by
  intro x y k hk _hxy
  simp

theorem zmodVectorTake_apply_eq_of_incrementDependsOnTake
    {m r k : Nat} {F : (Fin r → ZMod m) → (Fin r → ZMod m)}
    (hF : ZModVectorIncrementDependsOnTake F)
    (hk : k ≤ r) {x y : Fin r → ZMod m}
    (hxy : zmodVectorTake hk x = zmodVectorTake hk y) :
    zmodVectorTake hk (F x) = zmodVectorTake hk (F y) := by
  funext i
  have hir : i.val < r := lt_of_lt_of_le i.isLt hk
  have hpre :
      zmodVectorTake (Nat.le_of_lt hir) x =
        zmodVectorTake (Nat.le_of_lt hir) y := by
    funext j
    have hjk : j.val < k := lt_trans j.isLt i.isLt
    exact congrFun hxy ⟨j.val, hjk⟩
  have hcoord :
      x ⟨i.val, hir⟩ = y ⟨i.val, hir⟩ := by
    exact congrFun hxy i
  have hinc := hF x y i.val hir hpre
  change F x ⟨i.val, hir⟩ = F y ⟨i.val, hir⟩
  have hcalc :
      F x ⟨i.val, hir⟩ - x ⟨i.val, hir⟩ =
        F y ⟨i.val, hir⟩ - y ⟨i.val, hir⟩ := hinc
  rw [hcoord] at hcalc
  calc
    F x ⟨i.val, hir⟩
        = (F x ⟨i.val, hir⟩ - y ⟨i.val, hir⟩) +
            y ⟨i.val, hir⟩ := by
            abel
    _ = (F y ⟨i.val, hir⟩ - y ⟨i.val, hir⟩) +
            y ⟨i.val, hir⟩ := by
            rw [hcalc]
    _ = F y ⟨i.val, hir⟩ := by
            abel

theorem zmodVectorTake_extendZero_apply_bijective_of_incrementDependsOnTake
    {m r k : Nat} [NeZero m] (hk : k ≤ r)
    {F : (Fin r → ZMod m) → (Fin r → ZMod m)}
    (hF : ZModVectorIncrementDependsOnTake F)
    (hBij : Function.Bijective F) :
    Function.Bijective
      (fun x : Fin k → ZMod m =>
        zmodVectorTake hk (F (zmodVectorExtendZero hk x))) := by
  classical
  let G : (Fin k → ZMod m) → (Fin k → ZMod m) :=
    fun x => zmodVectorTake hk (F (zmodVectorExtendZero hk x))
  have hsurj : Function.Surjective G := by
    intro y
    rcases hBij.2 (zmodVectorExtendZero hk y) with ⟨xFull, hxFull⟩
    refine ⟨zmodVectorTake hk xFull, ?_⟩
    have htake :
        zmodVectorTake hk xFull =
          zmodVectorTake hk
            (zmodVectorExtendZero hk (zmodVectorTake hk xFull)) := by
      simp
    have hFtake :=
      zmodVectorTake_apply_eq_of_incrementDependsOnTake hF hk htake
    dsimp [G]
    rw [← hFtake]
    rw [hxFull]
    simp
  have hcard :
      Fintype.card (Fin k → ZMod m) =
        Fintype.card (Fin k → ZMod m) := rfl
  have hbijG : Function.Bijective G :=
    (Fintype.bijective_iff_surjective_and_card G).2 ⟨hsurj, hcard⟩
  simpa [G] using hbijG

theorem zmodVectorTake_extendZero_apply_bijective_of_take_preserving
    {m r k : Nat} [NeZero m] (hk : k ≤ r)
    {F : (Fin r → ZMod m) → (Fin r → ZMod m)}
    (hPres :
      ∀ x y : Fin r → ZMod m,
        zmodVectorTake hk x = zmodVectorTake hk y →
          zmodVectorTake hk (F x) = zmodVectorTake hk (F y))
    (hBij : Function.Bijective F) :
    Function.Bijective
      (fun x : Fin k → ZMod m =>
        zmodVectorTake hk (F (zmodVectorExtendZero hk x))) := by
  classical
  let G : (Fin k → ZMod m) → (Fin k → ZMod m) :=
    fun x => zmodVectorTake hk (F (zmodVectorExtendZero hk x))
  have hsurj : Function.Surjective G := by
    intro y
    rcases hBij.2 (zmodVectorExtendZero hk y) with ⟨xFull, hxFull⟩
    refine ⟨zmodVectorTake hk xFull, ?_⟩
    have htake :
        zmodVectorTake hk xFull =
          zmodVectorTake hk
            (zmodVectorExtendZero hk (zmodVectorTake hk xFull)) := by
      simp
    have hFtake := hPres xFull
      (zmodVectorExtendZero hk (zmodVectorTake hk xFull)) htake
    dsimp [G]
    rw [← hFtake]
    rw [hxFull]
    simp
  have hcard :
      Fintype.card (Fin k → ZMod m) =
        Fintype.card (Fin k → ZMod m) := rfl
  have hbijG : Function.Bijective G :=
    (Fintype.bijective_iff_surjective_and_card G).2 ⟨hsurj, hcard⟩
  simpa [G] using hbijG

theorem zmodVectorIncrementDependsOnTake_comp
    {m r : Nat} {F G : (Fin r → ZMod m) → (Fin r → ZMod m)}
    (hF : ZModVectorIncrementDependsOnTake F)
    (hG : ZModVectorIncrementDependsOnTake G) :
    ZModVectorIncrementDependsOnTake (fun x => G (F x)) := by
  intro x y k hk hxy
  have hFinc := hF x y k hk hxy
  have htakeF :
      zmodVectorTake (Nat.le_of_lt hk) (F x) =
        zmodVectorTake (Nat.le_of_lt hk) (F y) :=
    zmodVectorTake_apply_eq_of_incrementDependsOnTake hF
      (Nat.le_of_lt hk) hxy
  have hGinc := hG (F x) (F y) k hk htakeF
  calc
    G (F x) ⟨k, hk⟩ - x ⟨k, hk⟩
        =
        (G (F x) ⟨k, hk⟩ - F x ⟨k, hk⟩) +
          (F x ⟨k, hk⟩ - x ⟨k, hk⟩) := by
          abel
    _ =
        (G (F y) ⟨k, hk⟩ - F y ⟨k, hk⟩) +
          (F y ⟨k, hk⟩ - y ⟨k, hk⟩) := by
          rw [hGinc, hFinc]
    _ =
        G (F y) ⟨k, hk⟩ - y ⟨k, hk⟩ := by
          abel

theorem zmodVectorIncrementDependsOnTake_skewFiberIterate
    {Base : Type*} {m r : Nat}
    (baseStep : Base → Base)
    (fiberStep : Base → (Fin r → ZMod m) → (Fin r → ZMod m))
    (hfiber : ∀ base : Base,
      ZModVectorIncrementDependsOnTake (fiberStep base)) :
    ∀ n : Nat, ∀ base : Base,
      ZModVectorIncrementDependsOnTake
        (skewFiberIterate baseStep fiberStep n base)
  | 0, _base => zmodVectorIncrementDependsOnTake_id
  | n + 1, base => by
      change ZModVectorIncrementDependsOnTake
        (fun x => skewFiberIterate baseStep fiberStep n
          (baseStep base) (fiberStep base x))
      exact zmodVectorIncrementDependsOnTake_comp
        (hfiber base)
        (zmodVectorIncrementDependsOnTake_skewFiberIterate
          baseStep fiberStep hfiber n (baseStep base))

theorem skewFiberIterate_coord_eq_add_sum_range
    {Base : Type*} {m r : Nat}
    (baseStep : Base → Base)
    (fiberStep : Base → (Fin r → ZMod m) → (Fin r → ZMod m))
    (carry : Base → (Fin r → ZMod m) → ZMod m) (j : Fin r)
    (hstep : ∀ base fiber,
      fiberStep base fiber j = fiber j + carry base fiber) :
    ∀ n : Nat, ∀ base : Base, ∀ fiber : Fin r → ZMod m,
      skewFiberIterate baseStep fiberStep n base fiber j =
        fiber j +
          ∑ u ∈ Finset.range n,
            carry ((baseStep^[u]) base)
              (skewFiberIterate baseStep fiberStep u base fiber)
  | 0, _base, _fiber => by
      simp [skewFiberIterate]
  | n + 1, base, fiber => by
      rw [skewFiberIterate]
      rw [skewFiberIterate_coord_eq_add_sum_range
        baseStep fiberStep carry j hstep n (baseStep base)
        (fiberStep base fiber)]
      rw [hstep]
      let f : Nat → ZMod m := fun u =>
        carry ((baseStep^[u]) base)
          (skewFiberIterate baseStep fiberStep u base fiber)
      rw [Finset.sum_range_succ' f n]
      have hshift :
          (∑ u ∈ Finset.range n,
              carry ((baseStep^[u]) (baseStep base))
                (skewFiberIterate baseStep fiberStep u
                  (baseStep base) (fiberStep base fiber))) =
            ∑ u ∈ Finset.range n, f (u + 1) := by
        apply Finset.sum_congr rfl
        intro u _hu
        simp [f, skewFiberIterate, Function.iterate_succ_apply]
      rw [hshift]
      simp [f, skewFiberIterate]
      abel

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

theorem skewFiberAdditiveCarry_eq_sum_range {Base : Type*} {m : Nat}
    (baseStep : Base → Base) (carry : Base → ZMod m) :
    ∀ n : Nat, ∀ base : Base,
      skewFiberAdditiveCarry baseStep carry n base =
        ∑ i ∈ Finset.range n, carry ((baseStep^[i]) base)
  | 0, base => by simp [skewFiberAdditiveCarry]
  | n + 1, base => by
      rw [skewFiberAdditiveCarry]
      rw [skewFiberAdditiveCarry_eq_sum_range baseStep carry n (baseStep base)]
      have hsum :
          (∑ i ∈ Finset.range n, carry ((baseStep^[i]) (baseStep base))) =
            ∑ i ∈ Finset.range n, carry ((baseStep^[i + 1]) base) := by
        apply Finset.sum_congr rfl
        intro i _hi
        congr 1
      rw [hsum]
      rw [Finset.sum_range_succ']
      simp [add_comm]

theorem skewFiberAdditiveCarry_eq_univ_sum_of_rank_step
    {Base : Type*} [Fintype Base]
    {N m : Nat} [NeZero N]
    (baseStep : Base → Base) (rank : Base ≃ ZMod N)
    (carry : Base → ZMod m) (base : Base)
    (hstep : ∀ x : Base, rank (baseStep x) = rank x + 1) :
    skewFiberAdditiveCarry baseStep carry N base =
      ∑ x : Base, carry x := by
  classical
  calc
    skewFiberAdditiveCarry baseStep carry N base =
        ∑ i ∈ Finset.range N, carry ((baseStep^[i]) base) :=
      skewFiberAdditiveCarry_eq_sum_range baseStep carry N base
    _ = ∑ x ∈ (Finset.univ : Finset Base), carry x := by
      refine Finset.sum_bij
        (fun i _hi => (baseStep^[i]) base)
        (by intro i hi; simp)
        ?inj ?surj ?compat
      · intro i hi j hj hij
        have hiN : i < N := Finset.mem_range.mp hi
        have hjN : j < N := Finset.mem_range.mp hj
        have hrank : rank ((baseStep^[i]) base) =
            rank ((baseStep^[j]) base) := congrArg rank hij
        rw [iterate_rank_add_one baseStep rank hstep i base] at hrank
        rw [iterate_rank_add_one baseStep rank hstep j base] at hrank
        have hcast : (i : ZMod N) = (j : ZMod N) :=
          add_left_cancel hrank
        have hmod : i ≡ j [MOD N] :=
          (ZMod.natCast_eq_natCast_iff i j N).mp hcast
        unfold Nat.ModEq at hmod
        rwa [Nat.mod_eq_of_lt hiN, Nat.mod_eq_of_lt hjN] at hmod
      · intro x _hx
        rcases zmod_rank_orbit_cover_lt baseStep rank hstep base x with
          ⟨k, hk, hkx⟩
        exact ⟨k, Finset.mem_range.mpr hk, hkx⟩
      · intro i _hi
        rfl
    _ = ∑ x : Base, carry x := by simp

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

theorem sectionReturn_skewProductMap_zmod_add_single_cycle_of_unit
    {Base : Type*} {m : Nat} [NeZero m]
    (baseStep : Base → Base) (carry : Base → ZMod m)
    (base : Base) (period : Nat) (a : ZMod m)
    (ha : IsUnit a)
    (hcarry :
      skewFiberAdditiveCarry baseStep carry period base = a) :
    IsSingleCycleMap
      (sectionReturn
        (skewProductMap baseStep (fun b z => z + carry b))
        base period) := by
  rw [sectionReturn_skewProductMap_zmod_add]
  rw [hcarry]
  exact zmod_add_single_cycle_of_unit ha

noncomputable def sectionReturn_skewProductMap_zmod_add_cycleCoordinate_of_coprime
    {Base : Type*} {m : Nat} [NeZero m]
    (baseStep : Base → Base) (carry : Base → ZMod m)
    (base : Base) (period a : Nat)
    (ha : Nat.Coprime a m)
    (hcarry :
      skewFiberAdditiveCarry baseStep carry period base = (a : ZMod m)) :
    CycleCoordinate m
      (sectionReturn
        (skewProductMap baseStep (fun b z => z + carry b))
        base period) := by
  rw [sectionReturn_skewProductMap_zmod_add]
  rw [hcarry]
  exact CycleCoordinate.zmodAddConstOfCoprime ha

noncomputable def sectionReturn_skewProductMap_zmod_add_cycleCoordinate_of_unit
    {Base : Type*} {m : Nat} [NeZero m]
    (baseStep : Base → Base) (carry : Base → ZMod m)
    (base : Base) (period : Nat) (a : ZMod m)
    (ha : IsUnit a)
    (hcarry :
      skewFiberAdditiveCarry baseStep carry period base = a) :
    CycleCoordinate m
      (sectionReturn
        (skewProductMap baseStep (fun b z => z + carry b))
        base period) := by
  rw [sectionReturn_skewProductMap_zmod_add]
  rw [hcarry]
  exact CycleCoordinate.zmodAddConstOfUnit ha

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

noncomputable def cycleCoordinate_of_skewProduct_base_orbit_monodromy
    {Base Fiber : Type*} [Fintype Base] [Fintype Fiber]
    [DecidableEq Base] [DecidableEq Fiber]
    {n : Nat} [NeZero n]
    (baseStep : Base → Base) (fiberStep : Base → Fiber → Fiber)
    (base : Base) (period : Nat)
    (hcard : Fintype.card (Base × Fiber) = n)
    (hn : 1 < n)
    (hbase : Function.Bijective baseStep)
    (hfiber : ∀ u : Base, Function.Bijective (fiberStep u))
    (hreturnBase : (baseStep^[period]) base = base)
    (hbaseCover : ∀ b : Base, ∃ k : Nat,
      k < period ∧ (baseStep^[k]) base = b)
    (hmonodromy :
      IsSingleCycleMap
        (sectionReturn (skewProductMap baseStep fiberStep) base period)) :
    CycleCoordinate n (skewProductMap baseStep fiberStep) :=
  CycleCoordinate.ofFiniteSingleCycle
    (f := skewProductMap baseStep fiberStep)
    hcard hn
    (single_cycle_of_skewProduct_base_orbit_monodromy
      baseStep fiberStep base period hbase hfiber hreturnBase hbaseCover
      hmonodromy)

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

theorem single_cycle_of_skewProduct_zmod_additive_unit_carry
    {Base : Type*} {m : Nat} [NeZero m]
    (baseStep : Base → Base) (carry : Base → ZMod m)
    (base : Base) (period : Nat) (a : ZMod m)
    (hbase : Function.Bijective baseStep)
    (hreturnBase : (baseStep^[period]) base = base)
    (hbaseCover : ∀ b : Base, ∃ k : Nat,
      k < period ∧ (baseStep^[k]) base = b)
    (ha : IsUnit a)
    (hcarry :
      skewFiberAdditiveCarry baseStep carry period base = a) :
    IsSingleCycleMap
      (skewProductMap baseStep (fun b z => z + carry b)) :=
  single_cycle_of_skewProduct_base_orbit_monodromy
    baseStep (fun b z => z + carry b) base period
    hbase
    (fun b => zmod_add_const_bijective (carry b))
    hreturnBase hbaseCover
    (sectionReturn_skewProductMap_zmod_add_single_cycle_of_unit
      baseStep carry base period a ha hcarry)

theorem single_cycle_of_skewProduct_zmod_additive_carry_of_rank_unit_sum
    {Base : Type*} [Fintype Base]
    {N m : Nat} [NeZero N] [NeZero m]
    (baseStep : Base → Base) (rank : Base ≃ ZMod N)
    (carry : Base → ZMod m) (base : Base)
    (hstep : ∀ x : Base, rank (baseStep x) = rank x + 1)
    (hunit : IsUnit (∑ x : Base, carry x)) :
    IsSingleCycleMap
      (skewProductMap baseStep (fun b z => z + carry b)) :=
  single_cycle_of_skewProduct_zmod_additive_unit_carry
    baseStep carry base N (∑ x : Base, carry x)
    (single_cycle_of_zmod_rank_equiv baseStep rank hstep).1
    (zmod_rank_iterate_period baseStep rank hstep base)
    (zmod_rank_orbit_cover_lt baseStep rank hstep base)
    hunit
    (skewFiberAdditiveCarry_eq_univ_sum_of_rank_step
      baseStep rank carry base hstep)

noncomputable def cycleCoordinate_of_skewProduct_zmod_additive_carry
    {Base : Type*} [Fintype Base] [DecidableEq Base]
    {m n : Nat} [NeZero m] [NeZero n]
    (baseStep : Base → Base) (carry : Base → ZMod m)
    (base : Base) (period a : Nat)
    (hcard : Fintype.card (Base × ZMod m) = n)
    (hn : 1 < n)
    (hbase : Function.Bijective baseStep)
    (hreturnBase : (baseStep^[period]) base = base)
    (hbaseCover : ∀ b : Base, ∃ k : Nat,
      k < period ∧ (baseStep^[k]) base = b)
    (ha : Nat.Coprime a m)
    (hcarry :
      skewFiberAdditiveCarry baseStep carry period base = (a : ZMod m)) :
    CycleCoordinate n
      (skewProductMap baseStep (fun b z => z + carry b)) :=
  cycleCoordinate_of_skewProduct_base_orbit_monodromy
    baseStep (fun b z => z + carry b) base period
    hcard hn
    hbase
    (fun b => zmod_add_const_bijective (carry b))
    hreturnBase hbaseCover
    (sectionReturn_skewProductMap_zmod_add_single_cycle_of_coprime
      baseStep carry base period a ha hcarry)

noncomputable def cycleCoordinate_of_skewProduct_zmod_additive_unit_carry
    {Base : Type*} [Fintype Base] [DecidableEq Base]
    {m n : Nat} [NeZero m] [NeZero n]
    (baseStep : Base → Base) (carry : Base → ZMod m)
    (base : Base) (period : Nat) (a : ZMod m)
    (hcard : Fintype.card (Base × ZMod m) = n)
    (hn : 1 < n)
    (hbase : Function.Bijective baseStep)
    (hreturnBase : (baseStep^[period]) base = base)
    (hbaseCover : ∀ b : Base, ∃ k : Nat,
      k < period ∧ (baseStep^[k]) base = b)
    (ha : IsUnit a)
    (hcarry :
      skewFiberAdditiveCarry baseStep carry period base = a) :
    CycleCoordinate n
      (skewProductMap baseStep (fun b z => z + carry b)) :=
  cycleCoordinate_of_skewProduct_base_orbit_monodromy
    baseStep (fun b z => z + carry b) base period
    hcard hn
    hbase
    (fun b => zmod_add_const_bijective (carry b))
    hreturnBase hbaseCover
    (sectionReturn_skewProductMap_zmod_add_single_cycle_of_unit
      baseStep carry base period a ha hcarry)

noncomputable def cycleCoordinate_of_skewProduct_zmod_additive_carry_of_rank_unit_sum
    {Base : Type*} [Fintype Base] [DecidableEq Base]
    {N m n : Nat} [NeZero N] [NeZero m] [NeZero n]
    (baseStep : Base → Base) (rank : Base ≃ ZMod N)
    (carry : Base → ZMod m) (base : Base)
    (hcard : Fintype.card (Base × ZMod m) = n)
    (hn : 1 < n)
    (hstep : ∀ x : Base, rank (baseStep x) = rank x + 1)
    (hunit : IsUnit (∑ x : Base, carry x)) :
    CycleCoordinate n
      (skewProductMap baseStep (fun b z => z + carry b)) :=
  cycleCoordinate_of_skewProduct_zmod_additive_unit_carry
    baseStep carry base N (∑ x : Base, carry x)
    hcard hn
    (single_cycle_of_zmod_rank_equiv baseStep rank hstep).1
    (zmod_rank_iterate_period baseStep rank hstep base)
    (zmod_rank_orbit_cover_lt baseStep rank hstep base)
    hunit
    (skewFiberAdditiveCarry_eq_univ_sum_of_rank_step
      baseStep rank carry base hstep)

theorem zmodVectorLowerTriangularUnitCycleCoordinate :
    ZModVectorLowerTriangularUnitCycleCoordinateGoal := by
  intro m r _inst F gamma htri hunit
  classical
  by_cases hm1 : m = 1
  · subst m
    refine ⟨zmodVectorPowerEquiv r 1, ?_⟩
    intro x
    haveI : Subsingleton (ZMod (1 ^ r)) := by
      simpa using (inferInstance : Subsingleton (ZMod 1))
    exact Subsingleton.elim _ _
  · have hmgt : 1 < m := by
      have hm0 : m ≠ 0 := NeZero.ne m
      omega
    induction r with
    | zero =>
        refine ⟨zmodVectorPowerEquiv 0 m, ?_⟩
        intro x
        haveI : Subsingleton (ZMod (m ^ 0)) := by
          simpa using (inferInstance : Subsingleton (ZMod 1))
        exact Subsingleton.elim _ _
    | succ n ih =>
        let Base := Fin n → ZMod m
        let baseStep : Base → Base := fun u =>
          zmodVectorTake (m := m) (r := n + 1) (k := n)
            (Nat.le_succ n) (F (Fin.snoc u 0))
        let carry : Base → ZMod m := fun u =>
          gamma n (Nat.lt_succ_self n) u
        let gammaBase :
            ∀ k : Nat, k < n → (Fin k → ZMod m) → ZMod m :=
          fun k hk => gamma k (lt_of_lt_of_le hk (Nat.le_succ n))
        have htriBase :
            ∀ x : Fin n → ZMod m, ∀ k : Nat, ∀ hk : k < n,
              baseStep x ⟨k, hk⟩ =
                x ⟨k, hk⟩ +
                  gammaBase k hk (zmodVectorTake (Nat.le_of_lt hk) x) := by
          intro x k hk
          have hk' : k < n + 1 := lt_of_lt_of_le hk (Nat.le_succ n)
          have h := htri (Fin.snoc x (0 : ZMod m)) k hk'
          have hsnoc :
              (@Fin.snoc n (fun _ => ZMod m) x (0 : ZMod m))
                ⟨k, hk'⟩ = x ⟨k, hk⟩ := by
            have hidx :
                (⟨k, hk'⟩ : Fin (n + 1)) =
                  (⟨k, hk⟩ : Fin n).castSucc := rfl
            rw [hidx]
            exact Fin.snoc_castSucc
              (α := fun _ : Fin (n + 1) => ZMod m) (0 : ZMod m) x ⟨k, hk⟩
          have htake :
              zmodVectorTake (Nat.le_of_lt hk') (Fin.snoc x (0 : ZMod m)) =
                zmodVectorTake (Nat.le_of_lt hk) x := by
            simpa using
              zmodVectorTake_snoc (m := m) (n := n) (k := k)
                (Nat.le_of_lt hk) x (0 : ZMod m)
          change F (Fin.snoc x (0 : ZMod m))
              (⟨k, lt_of_lt_of_le hk (Nat.le_succ n)⟩ : Fin (n + 1)) =
            x ⟨k, hk⟩ +
              gammaBase k hk (zmodVectorTake (Nat.le_of_lt hk) x)
          rw [h, hsnoc, htake]
        have hunitBase :
            ∀ k : Nat, ∀ hk : k < n,
              IsUnit (∑ x : (Fin k → ZMod m), gammaBase k hk x) := by
          intro k hk
          exact hunit k (lt_of_lt_of_le hk (Nat.le_succ n))
        rcases ih baseStep gammaBase htriBase hunitBase with
          ⟨rankBase, hrankBase⟩
        have hcard :
            Fintype.card (Base × ZMod m) = m ^ (n + 1) := by
          simp [Base, pow_succ]
        have hncard : 1 < m ^ (n + 1) :=
          one_lt_pow₀ hmgt (Nat.succ_ne_zero n)
        let C : CycleCoordinate (m ^ (n + 1))
            (skewProductMap baseStep (fun b z => z + carry b)) :=
          cycleCoordinate_of_skewProduct_zmod_additive_carry_of_rank_unit_sum
            (N := m ^ n) (m := m) (n := m ^ (n + 1))
            baseStep rankBase carry (0 : Base)
            hcard hncard hrankBase
            (hunit n (Nat.lt_succ_self n))
        let eSplit := zmodVectorSnocEquiv n m
        let S := skewProductMap baseStep (fun b z => z + carry b)
        have hconjPair :
            ∀ p : Base × ZMod m, eSplit (F (eSplit.symm p)) = S p := by
          intro p
          rcases p with ⟨u, a⟩
          ext i
          · have hk' : i.val < n + 1 :=
              lt_of_lt_of_le i.isLt (Nat.le_succ n)
            have hidx :
                i.castSucc = (⟨i.val, hk'⟩ : Fin (n + 1)) := rfl
            have htake_a :
                zmodVectorTake (Nat.le_of_lt hk') (Fin.snoc u a) =
                  zmodVectorTake (Nat.le_of_lt i.isLt) u := by
              simp
            have htake_0 :
                zmodVectorTake (Nat.le_of_lt hk') (Fin.snoc u (0 : ZMod m)) =
                  zmodVectorTake (Nat.le_of_lt i.isLt) u := by
              simp
            have hsnoc_a :
                (@Fin.snoc n (fun _ => ZMod m) u a) ⟨i.val, hk'⟩ = u i := by
              rw [show (⟨i.val, hk'⟩ : Fin (n + 1)) = i.castSucc by rfl]
              exact Fin.snoc_castSucc
                (α := fun _ : Fin (n + 1) => ZMod m) a u i
            have hsnoc_0 :
                (@Fin.snoc n (fun _ => ZMod m) u (0 : ZMod m))
                  ⟨i.val, hk'⟩ = u i := by
              rw [show (⟨i.val, hk'⟩ : Fin (n + 1)) = i.castSucc by rfl]
              exact Fin.snoc_castSucc
                (α := fun _ : Fin (n + 1) => ZMod m) (0 : ZMod m) u i
            have hFa := htri (Fin.snoc u a) i.val hk'
            have hF0 := htri (Fin.snoc u (0 : ZMod m)) i.val hk'
            have eqFa :
                F (Fin.snoc u a) ⟨i.val, hk'⟩ =
                  u i + gamma i.val hk'
                    (zmodVectorTake (Nat.le_of_lt i.isLt) u) := by
              rw [hFa, hsnoc_a, htake_a]
            have eqF0 :
                F (Fin.snoc u (0 : ZMod m)) ⟨i.val, hk'⟩ =
                  u i + gamma i.val hk'
                    (zmodVectorTake (Nat.le_of_lt i.isLt) u) := by
              rw [hF0, hsnoc_0, htake_0]
            change F (Fin.snoc u a) i.castSucc =
              F (Fin.snoc u (0 : ZMod m)) i.castSucc
            rw [hidx]
            exact eqFa.trans eqF0.symm
          · have hlast := htri (Fin.snoc u a) n (Nat.lt_succ_self n)
            have htake :
                zmodVectorTake (Nat.le_of_lt (Nat.lt_succ_self n))
                    (Fin.snoc u a) = u := by
              simp
            have hsnocLast :
                (@Fin.snoc n (fun _ => ZMod m) u a)
                  ⟨n, Nat.lt_succ_self n⟩ = a := by
              change (@Fin.snoc n (fun _ => ZMod m) u a) (Fin.last n) = a
              exact Fin.snoc_last (α := fun _ : Fin (n + 1) => ZMod m) a u
            change F (Fin.snoc u a) ⟨n, Nat.lt_succ_self n⟩ = a + carry u
            rw [hlast, htake, hsnocLast]
        refine ⟨eSplit.trans C.equiv.symm, ?_⟩
        intro x
        have hx : eSplit (F x) = S (eSplit x) := by
          simpa using hconjPair (eSplit x)
        have hstep := CycleCoordinate.rank_step C (eSplit x)
        change C.equiv.symm (eSplit (F x)) = C.equiv.symm (eSplit x) + 1
        rw [hx]
        simpa [S] using hstep

end Shared
