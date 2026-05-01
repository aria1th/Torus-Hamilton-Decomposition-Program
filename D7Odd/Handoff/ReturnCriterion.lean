import D7Odd.Basic
import Shared.RootFlat
import Shared.RankCycle

namespace D7Odd
namespace Handoff

abbrev Color := Fin 7

abbrev Direction := Fin 7

def IsSingleCycleMap {α : Type*} (f : α → α) : Prop :=
  Function.Bijective f ∧ ∀ x y : α, ∃ n : Nat, f^[n] x = y

def addQ (m : Nat) (i : Direction) (w : Vec7 m) : Vec7 m :=
  w + q7 m i

def subQ (m : Nat) (i : Direction) (w : Vec7 m) : Vec7 m :=
  w - q7 m i

abbrev RootState7 (m : Nat) := {w : Vec7 m // Root7 m w}

theorem sum7_add' (m : Nat) (x y : Vec7 m) :
    sum7 m (x + y) = sum7 m x + sum7 m y := by
  simp [sum7, Finset.sum_add_distrib]

theorem sum7_sub' (m : Nat) (x y : Vec7 m) :
    sum7 m (x - y) = sum7 m x - sum7 m y := by
  simp [sum7, Finset.sum_sub_distrib]

theorem sum7_q7_zero (m : Nat) (i : Fin 7) :
    sum7 m (q7 m i) = 0 := by
  simp [sum7, q7, e7, Finset.sum_sub_distrib]

def addQRoot (m : Nat) (i : Direction) (w : RootState7 m) : RootState7 m :=
  ⟨addQ m i w.1, by
    unfold Root7 addQ
    rw [sum7_add', w.2, sum7_q7_zero]
    simp⟩

def subQRoot (m : Nat) (i : Direction) (w : RootState7 m) : RootState7 m :=
  ⟨subQ m i w.1, by
    unfold Root7 subQ
    rw [sum7_sub', w.2, sum7_q7_zero]
    simp⟩

theorem subQRoot_addQRoot {m : Nat} (i : Fin 7) (w : RootState7 m) :
    subQRoot m i (addQRoot m i w) = w := by
  apply Subtype.ext
  ext j
  simp [subQRoot, addQRoot, subQ, addQ]

theorem addQRoot_subQRoot {m : Nat} (i : Fin 7) (w : RootState7 m) :
    addQRoot m i (subQRoot m i w) = w := by
  apply Subtype.ext
  ext j
  simp [subQRoot, addQRoot, subQ, addQ]

theorem bijective_of_inverse
    {α β : Type*} (f : α → β) (g : β → α)
    (hleft : ∀ x : α, g (f x) = x)
    (hright : ∀ y : β, f (g y) = y) :
    Function.Bijective f := by
  constructor
  · intro x y hxy
    calc
      x = g (f x) := (hleft x).symm
      _ = g (f y) := by rw [hxy]
      _ = y := hleft y
  · intro y
    exact ⟨g y, hright y⟩

theorem addQRoot_bijective {m : Nat} (i : Fin 7) :
    Function.Bijective (addQRoot m i) :=
  bijective_of_inverse (addQRoot m i) (subQRoot m i)
    (subQRoot_addQRoot i) (addQRoot_subQRoot i)

structure RootFlatSchedule (m : Nat) where
  dir : ZMod m → RootState7 m → Color → Direction

namespace RootFlatSchedule

def rowLatin {m : Nat} (S : RootFlatSchedule m) : Prop :=
  ∀ t w, Function.Bijective fun c : Color => S.dir t w c

def layerMap {m : Nat} (S : RootFlatSchedule m) (t : ZMod m) (c : Color) :
    RootState7 m → RootState7 m :=
  fun w => addQRoot m (S.dir t w c) w

def layerBijective {m : Nat} (S : RootFlatSchedule m) : Prop :=
  ∀ t c, Function.Bijective (S.layerMap t c)

def returnMap {m : Nat} [NeZero m] (S : RootFlatSchedule m) (c : Color) :
    RootState7 m → RootState7 m :=
  fun w => ((List.range m).foldl (fun x (t : Nat) => S.layerMap (t : ZMod m) c x) w)

def returnsSingleCycle {m : Nat} [NeZero m] (S : RootFlatSchedule m) : Prop :=
  ∀ c : Color, IsSingleCycleMap (S.returnMap c)

end RootFlatSchedule

namespace RootFlatSchedule

def toShared {m : Nat} (S : RootFlatSchedule m) :
    Shared.RootFlatSchedule Color Direction (RootState7 m) m where
  dir := S.dir
  step := fun i w => addQRoot m i w

theorem toShared_rowLatin {m : Nat} (S : RootFlatSchedule m) :
    S.toShared.rowLatin ↔ S.rowLatin := by
  rfl

theorem toShared_layerMap {m : Nat} (S : RootFlatSchedule m)
    (t : ZMod m) (c : Color) (w : RootState7 m) :
    S.toShared.layerMap t c w = S.layerMap t c w := by
  rfl

theorem toShared_layerBijective {m : Nat} (S : RootFlatSchedule m) :
    S.toShared.layerBijective ↔ S.layerBijective := by
  rfl

theorem toShared_returnMap {m : Nat} [NeZero m]
    (S : RootFlatSchedule m) (c : Color) :
    S.toShared.returnMap c = S.returnMap c := by
  funext w
  rfl

theorem toShared_returnsSingleCycle {m : Nat} [NeZero m]
    (S : RootFlatSchedule m) :
    S.toShared.returnsSingleCycle ↔ S.returnsSingleCycle := by
  constructor
  · intro h c
    simpa [toShared_returnMap S c, Shared.IsSingleCycleMap, IsSingleCycleMap]
      using h c
  · intro h c
    simpa [toShared_returnMap S c, Shared.IsSingleCycleMap, IsSingleCycleMap]
      using h c

end RootFlatSchedule

structure RootFlatCertificate (m : Nat) [NeZero m] where
  schedule : RootFlatSchedule m
  rowLatin : schedule.rowLatin
  layerBijective : schedule.layerBijective
  returnsSingleCycle : schedule.returnsSingleCycle

namespace RootFlatCertificate

def toShared {m : Nat} [NeZero m] (cert : RootFlatCertificate m) :
    Shared.RootFlatCertificate Color Direction (RootState7 m) m where
  schedule := cert.schedule.toShared
  rowLatin := (RootFlatSchedule.toShared_rowLatin cert.schedule).2
    cert.rowLatin
  layerBijective := (RootFlatSchedule.toShared_layerBijective cert.schedule).2
    cert.layerBijective
  returnsSingleCycle :=
    (RootFlatSchedule.toShared_returnsSingleCycle cert.schedule).2
      cert.returnsSingleCycle

end RootFlatCertificate

def HamiltonDecompositionD7 (m : Nat) [NeZero m] : Prop :=
  Nonempty (RootFlatCertificate m)

theorem certificate_implies_hamilton {m : Nat} [NeZero m]
    (cert : RootFlatCertificate m) :
    HamiltonDecompositionD7 m := by
  exact ⟨cert⟩

theorem rootFlatReturnCriterion_of_hamiltonDecompositionD7
    {m : Nat} [NeZero m] (h : HamiltonDecompositionD7 m) :
    Shared.RootFlatReturnCriterion Color Direction (RootState7 m) m := by
  rcases h with ⟨cert⟩
  exact Shared.rootFlatReturnCriterion_of_schedule
    ((RootFlatSchedule.toShared_rowLatin cert.schedule).2 cert.rowLatin)
    ((RootFlatSchedule.toShared_layerBijective cert.schedule).2
      cert.layerBijective)
    ((RootFlatSchedule.toShared_returnsSingleCycle cert.schedule).2
      cert.returnsSingleCycle)

theorem iterate_rank_add_one
    {α : Type*} {N : Nat} [NeZero N] (f : α → α) (rank : α → ZMod N)
    (hstep : ∀ x : α, rank (f x) = rank x + 1) :
    ∀ n : Nat, ∀ x : α, rank (f^[n] x) = rank x + (n : ZMod N) :=
  Shared.iterate_rank_add_one f rank hstep

theorem single_cycle_of_zmod_rank
    {α : Type*} {N : Nat} [NeZero N] (f : α → α) (rank : α → ZMod N)
    (hrank : Function.Bijective rank)
    (hstep : ∀ x : α, rank (f x) = rank x + 1) :
    IsSingleCycleMap f := by
  have h := Shared.single_cycle_of_zmod_rank f rank hrank hstep
  simpa [Shared.IsSingleCycleMap, IsSingleCycleMap] using h

theorem zmod_add_single_cycle_of_coprime
    {m a : Nat} [NeZero m] (ha : Nat.Coprime a m) :
    IsSingleCycleMap (fun x : ZMod m => x + (a : ZMod m)) := by
  have h := Shared.zmod_add_single_cycle_of_coprime (m := m) (a := a) ha
  simpa [Shared.IsSingleCycleMap, IsSingleCycleMap] using h

theorem zmod_affine_mul_right_bijective
    {m a : Nat} [NeZero m] (ha : Nat.Coprime a m) (offset : ZMod m) :
    Function.Bijective (fun x : ZMod m => offset + x * (a : ZMod m)) := by
  let u : (ZMod m)ˣ := ZMod.unitOfCoprime a ha
  have hu : (u : ZMod m) = (a : ZMod m) := by
    exact ZMod.coe_unitOfCoprime a ha
  refine bijective_of_inverse
    (fun x : ZMod m => offset + x * (a : ZMod m))
    (fun y : ZMod m => (y - offset) * (u⁻¹ : ZMod m))
    ?_ ?_
  · intro x
    rw [← hu]
    simp
  · intro y
    rw [← hu]
    simp

theorem zmod_affine_range_countP_eq_one
    {m a : Nat} [NeZero m] (ha : Nat.Coprime a m)
    (offset target : ZMod m) :
    (List.range m).countP
        (fun j : Nat => decide (offset + (j : ZMod m) * (a : ZMod m) = target)) = 1 := by
  let u : (ZMod m)ˣ := ZMod.unitOfCoprime a ha
  let x : ZMod m := (target - offset) * (u⁻¹ : ZMod m)
  have hu : (u : ZMod m) = (a : ZMod m) := by
    exact ZMod.coe_unitOfCoprime a ha
  have hx : offset + x * (a : ZMod m) = target := by
    dsimp [x]
    rw [← hu]
    simp
  have hbij := zmod_affine_mul_right_bijective (m := m) (a := a) ha offset
  have hfilter :
      (Finset.range m).filter
          (fun j : Nat => offset + (j : ZMod m) * (a : ZMod m) = target) =
        {x.val} := by
    ext j
    constructor
    · intro hj
      rcases (Finset.mem_filter.mp hj) with ⟨hjlt, hj⟩
      have hjmap :
          (fun y : ZMod m => offset + y * (a : ZMod m)) (j : ZMod m) =
            (fun y : ZMod m => offset + y * (a : ZMod m)) x := by
        change offset + (j : ZMod m) * (a : ZMod m) =
          offset + x * (a : ZMod m)
        rw [hj, hx]
      have hjx : (j : ZMod m) = x := hbij.1 hjmap
      have hjval : j = x.val := by
        simpa [ZMod.val_natCast_of_lt (Finset.mem_range.mp hjlt)]
          using congrArg ZMod.val hjx
      simp [hjval]
    · intro hj
      have hjval : j = x.val := by
        simpa using hj
      subst j
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr (ZMod.val_lt x)
      · simpa [ZMod.natCast_zmod_val] using hx
  have hcard :
      ((Finset.range m).filter
          (fun j : Nat => offset + (j : ZMod m) * (a : ZMod m) = target)).card = 1 := by
    rw [hfilter]
    simp
  rw [List.countP_eq_length_filter]
  have hnodup :
      (List.filter
        (fun j : Nat => decide (offset + (j : ZMod m) * (a : ZMod m) = target))
        (List.range m)).Nodup :=
    List.Nodup.filter _ List.nodup_range
  have htoFinset := List.toFinset_card_of_nodup hnodup
  rw [← htoFinset]
  rw [List.toFinset_filter, List.toFinset_range]
  simpa [decide_eq_true_eq] using hcard

theorem zmod_sum_range_indicator_eq_countP
    {m : Nat} [NeZero m] (p : Nat → Prop) [DecidablePred p] :
    (Finset.sum (Finset.range m)
      (fun j : Nat => if p j then (1 : ZMod m) else 0)) =
      ((List.range m).countP (fun j : Nat => decide (p j)) : ZMod m) := by
  rw [List.countP_eq_length_filter]
  have hnodup :
      (List.filter (fun j : Nat => decide (p j)) (List.range m)).Nodup :=
    List.Nodup.filter _ List.nodup_range
  have hcard := List.toFinset_card_of_nodup hnodup
  have hfilter :
      (List.filter (fun j : Nat => decide (p j)) (List.range m)).toFinset =
        (Finset.range m).filter p := by
    rw [List.toFinset_filter, List.toFinset_range]
    ext j
    simp [decide_eq_true_eq]
  rw [← hcard, hfilter]
  exact Finset.sum_boole p (Finset.range m)

theorem zmod_list_range_sum_eq_finset_sum
    {m n : Nat} (f : Nat → ZMod m) :
    ((List.range n).map f).sum = Finset.sum (Finset.range n) f := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      rw [Finset.sum_range_succ]
      simp [ih]

theorem zmod_int_add_single_cycle_of_coprime_abs
    {m : Nat} [NeZero m] (a : Int) (ha : Nat.Coprime a.natAbs m) :
    IsSingleCycleMap (fun x : ZMod m => x + (a : ZMod m)) := by
  have haI : IsCoprime a (m : Int) := by
    rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
    exact ha
  let u : (ZMod m)ˣ := ZMod.unitOfIsCoprime a haI
  refine single_cycle_of_zmod_rank
    (f := fun x : ZMod m => x + (a : ZMod m))
    (rank := fun x : ZMod m => (u⁻¹ : ZMod m) * x)
    ?_ ?_
  · exact Equiv.bijective (Units.mulLeft u⁻¹)
  · intro x
    have hu : (u : ZMod m) = (a : ZMod m) := by
      exact ZMod.coe_unitOfIsCoprime a haI
    calc
      (u⁻¹ : ZMod m) * (x + (a : ZMod m)) =
          (u⁻¹ : ZMod m) * x + (u⁻¹ : ZMod m) * (a : ZMod m) := by ring
      _ = (u⁻¹ : ZMod m) * x + (u⁻¹ : ZMod m) * (u : ZMod m) := by rw [hu]
      _ = (u⁻¹ : ZMod m) * x + 1 := by simp

theorem zmod_int_affine_mul_right_bijective
    {m : Nat} [NeZero m] (a : Int) (ha : Nat.Coprime a.natAbs m)
    (offset : ZMod m) :
    Function.Bijective (fun x : ZMod m => offset + x * (a : ZMod m)) := by
  have haI : IsCoprime a (m : Int) := by
    rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
    exact ha
  let u : (ZMod m)ˣ := ZMod.unitOfIsCoprime a haI
  have hu : (u : ZMod m) = (a : ZMod m) := by
    exact ZMod.coe_unitOfIsCoprime a haI
  refine bijective_of_inverse
    (fun x : ZMod m => offset + x * (a : ZMod m))
    (fun y : ZMod m => (y - offset) * (u⁻¹ : ZMod m))
    ?_ ?_
  · intro x
    rw [← hu]
    simp
  · intro y
    rw [← hu]
    simp

theorem singleCycle_of_rankFun
    {N : Nat} [NeZero N]
    (next rank : Fin N → Fin N)
    (hRank : Function.Bijective rank)
    (hStep : ∀ i, rank (next i) = rank i + 1) :
    IsSingleCycleMap next := by
  refine single_cycle_of_zmod_rank
    (f := next)
    (rank := fun i => (ZMod.finEquiv N) (rank i))
    ?_ ?_
  · exact Function.Bijective.comp (Equiv.bijective (ZMod.finEquiv N).toEquiv) hRank
  · intro i
    have h := congrArg (fun r => (ZMod.finEquiv N) r) (hStep i)
    simpa using h

theorem single_cycle_of_bijective_semiconj
    {α β : Type*} (f : α → α) (g : β → β) (φ : α → β)
    (hφ : Function.Bijective φ)
    (hcomm : ∀ x : α, φ (f x) = g (φ x))
    (hf : IsSingleCycleMap f) :
    IsSingleCycleMap g := by
  have hcomm_iter : ∀ (n : Nat) (x : α), φ (f^[n] x) = g^[n] (φ x) := by
    intro n x
    induction n generalizing x with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hcomm, ih]
  have hg_inj : Function.Injective g := by
    intro y₁ y₂ hy
    rcases hφ.2 y₁ with ⟨x₁, rfl⟩
    rcases hφ.2 y₂ with ⟨x₂, rfl⟩
    rw [← hcomm x₁, ← hcomm x₂] at hy
    exact congrArg φ (hf.1.1 (hφ.1 hy))
  have hg_surj : Function.Surjective g := by
    intro y
    rcases hφ.2 y with ⟨x, rfl⟩
    rcases hf.1.2 x with ⟨x₀, hx₀⟩
    refine ⟨φ x₀, ?_⟩
    rw [← hcomm, hx₀]
  refine ⟨⟨hg_inj, hg_surj⟩, ?_⟩
  intro y₁ y₂
  rcases hφ.2 y₁ with ⟨x₁, rfl⟩
  rcases hφ.2 y₂ with ⟨x₂, rfl⟩
  rcases hf.2 x₁ x₂ with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [← hcomm_iter, hn]

theorem single_cycle_of_return_cover
    {α σ : Type*} (f : α → α) (base : σ → α)
    (next : σ → σ) (time : σ → Nat)
    (hf : Function.Bijective f)
    (hreturn : ∀ s : σ, f^[time s] (base s) = base (next s))
    (hcover : ∀ x : α, ∃ s : σ, ∃ k : Nat,
      k < time s ∧ f^[k] (base s) = x)
    (hnext : IsSingleCycleMap next) :
    IsSingleCycleMap f := by
  refine ⟨hf, ?_⟩
  have hbase : ∀ (s : σ) (n : Nat),
      ∃ N : Nat, f^[N] (base s) = base (next^[n] s) := by
    intro s n
    induction n with
    | zero =>
        exact ⟨0, rfl⟩
    | succ n ih =>
        rcases ih with ⟨N, hN⟩
        let u : σ := next^[n] s
        refine ⟨time u + N, ?_⟩
        calc
          f^[time u + N] (base s) = f^[time u] (f^[N] (base s)) := by
            rw [Function.iterate_add_apply]
          _ = f^[time u] (base u) := by rw [hN]
          _ = base (next u) := hreturn u
          _ = base (next^[n.succ] s) := by
            rw [Function.iterate_succ_apply']
  intro x y
  rcases hcover x with ⟨sx, kx, hkx, hx⟩
  rcases hcover y with ⟨sy, ky, _hky, hy⟩
  let A := time sx - kx
  have hfromx : f^[A] x = base (next sx) := by
    rw [← hx]
    change f^[time sx - kx] (f^[kx] (base sx)) = base (next sx)
    rw [← Function.iterate_add_apply]
    rw [Nat.sub_add_cancel (Nat.le_of_lt hkx)]
    exact hreturn sx
  rcases hnext.2 (next sx) sy with ⟨r, hr⟩
  rcases hbase (next sx) r with ⟨N, hN⟩
  have htoSy : f^[N] (base (next sx)) = base sy := by
    rw [hN, hr]
  refine ⟨ky + (N + A), ?_⟩
  calc
    f^[ky + (N + A)] x = f^[ky] (f^[N + A] x) := by
      rw [Function.iterate_add_apply]
    _ = f^[ky] (base sy) := by
      congr
      calc
        f^[N + A] x = f^[N] (f^[A] x) := by
          rw [Function.iterate_add_apply]
        _ = f^[N] (base (next sx)) := by rw [hfromx]
        _ = base sy := htoSy
    _ = y := hy

abbrev ReturnSeg (σ : Type*) (time : σ → Nat) :=
  Sigma fun s : σ => Fin (time s)

def returnSegPoint {α σ : Type*} (f : α → α) (base : σ → α)
    (time : σ → Nat) (u : ReturnSeg σ time) : α :=
  f^[u.2.val] (base u.1)

theorem returnSegPoint_injective
    {α σ : Type*}
    (f : α → α) (base : σ → α) (time : σ → Nat)
    (hf : Function.Bijective f)
    (hbase_inj : Function.Injective base)
    (hfirst : ∀ s : σ, ∀ k : Nat, 0 < k → k < time s →
      ¬ ∃ t : σ, f^[k] (base s) = base t) :
    Function.Injective (returnSegPoint f base time) := by
  intro u v huv
  rcases u with ⟨su, ku⟩
  rcases v with ⟨sv, kv⟩
  dsimp [returnSegPoint] at huv
  by_cases hle : ku.val ≤ kv.val
  · have hv_decomp :
        (f^[kv.val]) (base sv) =
          (f^[ku.val]) ((f^[kv.val - ku.val]) (base sv)) := by
      conv_lhs => rw [show kv.val = ku.val + (kv.val - ku.val) by omega]
      rw [Function.iterate_add_apply]
    have hEqIter :
        (f^[ku.val]) (base su) =
          (f^[ku.val]) ((f^[kv.val - ku.val]) (base sv)) := by
      rw [← hv_decomp]
      exact huv
    have hbase :
        base su = (f^[kv.val - ku.val]) (base sv) :=
      (Function.Injective.iterate hf.1 ku.val) hEqIter
    by_cases hd : kv.val - ku.val = 0
    · have hkv : kv.val = ku.val := by omega
      have hst : su = sv := by
        apply hbase_inj
        simpa [hd] using hbase
      subst sv
      have hfin : ku = kv := by
        apply Fin.ext
        exact hkv.symm
      cases hfin
      rfl
    · exfalso
      have hpos : 0 < kv.val - ku.val := by omega
      have hlt : kv.val - ku.val < time sv := by
        have := kv.isLt
        omega
      exact (hfirst sv (kv.val - ku.val) hpos hlt) ⟨su, hbase.symm⟩
  · have hle' : kv.val ≤ ku.val := by omega
    have hu_decomp :
        (f^[ku.val]) (base su) =
          (f^[kv.val]) ((f^[ku.val - kv.val]) (base su)) := by
      conv_lhs => rw [show ku.val = kv.val + (ku.val - kv.val) by omega]
      rw [Function.iterate_add_apply]
    have hEqIter :
        (f^[kv.val]) ((f^[ku.val - kv.val]) (base su)) =
          (f^[kv.val]) (base sv) := by
      rw [← hu_decomp]
      exact huv
    have hbase :
        (f^[ku.val - kv.val]) (base su) = base sv :=
      (Function.Injective.iterate hf.1 kv.val) hEqIter
    by_cases hd : ku.val - kv.val = 0
    · have hku : ku.val = kv.val := by omega
      have hst : su = sv := by
        apply hbase_inj
        simpa [hd] using hbase
      subst sv
      have hfin : ku = kv := by
        apply Fin.ext
        exact hku
      cases hfin
      rfl
    · exfalso
      have hpos : 0 < ku.val - kv.val := by omega
      have hlt : ku.val - kv.val < time su := by
        have := ku.isLt
        omega
      exact (hfirst su (ku.val - kv.val) hpos hlt) ⟨sv, hbase⟩

theorem returnSegPoint_bijective_of_first_return_sum
    {α σ : Type*} [Fintype α] [Fintype σ]
    (f : α → α) (base : σ → α) (time : σ → Nat)
    (hf : Function.Bijective f)
    (hbase_inj : Function.Injective base)
    (hfirst : ∀ s : σ, ∀ k : Nat, 0 < k → k < time s →
      ¬ ∃ t : σ, f^[k] (base s) = base t)
    (hsum : (Finset.univ.sum fun s : σ => time s) = Fintype.card α) :
    Function.Bijective (returnSegPoint f base time) := by
  apply (Fintype.bijective_iff_injective_and_card
    (returnSegPoint f base time)).2
  refine ⟨returnSegPoint_injective f base time hf hbase_inj hfirst, ?_⟩
  calc
    Fintype.card (ReturnSeg σ time) =
        Finset.univ.sum fun s : σ => Fintype.card (Fin (time s)) := by
          simp [ReturnSeg, Fintype.card_sigma]
    _ = Finset.univ.sum fun s : σ => time s := by
          simp
    _ = Fintype.card α := hsum

theorem return_cover_of_first_return_sum
    {α σ : Type*} [Fintype α] [Fintype σ]
    (f : α → α) (base : σ → α) (time : σ → Nat)
    (hf : Function.Bijective f)
    (hbase_inj : Function.Injective base)
    (hfirst : ∀ s : σ, ∀ k : Nat, 0 < k → k < time s →
      ¬ ∃ t : σ, f^[k] (base s) = base t)
    (hsum : (Finset.univ.sum fun s : σ => time s) = Fintype.card α) :
    ∀ x : α, ∃ s : σ, ∃ k : Nat,
      k < time s ∧ f^[k] (base s) = x := by
  intro x
  rcases (returnSegPoint_bijective_of_first_return_sum
      f base time hf hbase_inj hfirst hsum).2 x with ⟨u, hu⟩
  exact ⟨u.1, u.2.val, u.2.isLt, hu⟩

theorem single_cycle_of_first_return_sum
    {α σ : Type*} [Fintype α] [Fintype σ]
    (f : α → α) (base : σ → α)
    (next : σ → σ) (time : σ → Nat)
    (hf : Function.Bijective f)
    (hbase_inj : Function.Injective base)
    (hreturn : ∀ s : σ, f^[time s] (base s) = base (next s))
    (hfirst : ∀ s : σ, ∀ k : Nat, 0 < k → k < time s →
      ¬ ∃ t : σ, f^[k] (base s) = base t)
    (hnext : IsSingleCycleMap next)
    (hsum : (Finset.univ.sum fun s : σ => time s) = Fintype.card α) :
    IsSingleCycleMap f := by
  exact single_cycle_of_return_cover f base next time hf hreturn
    (return_cover_of_first_return_sum f base time hf hbase_inj hfirst hsum)
    hnext

theorem single_cycle_of_fiber_return
    {α β σ : Type*} (f : α → α) (g : β → β) (proj : α → β)
    (fiberBase : σ → α) (fiberNext : σ → σ) (returnTime : Nat) (b₀ : β)
    (hf : Function.Bijective f)
    (hcomm : ∀ x : α, proj (f x) = g (proj x))
    (hfiber_surj : ∀ x : α, proj x = b₀ → ∃ s : σ, fiberBase s = x)
    (hreturn : ∀ s : σ, f^[returnTime] (fiberBase s) = fiberBase (fiberNext s))
    (hbase : IsSingleCycleMap g)
    (hfiber : IsSingleCycleMap fiberNext) :
    IsSingleCycleMap f := by
  have hcomm_iter : ∀ (n : Nat) (x : α), proj (f^[n] x) = g^[n] (proj x) := by
    intro n x
    induction n generalizing x with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hcomm, ih]
  have hreturn_iter : ∀ (n : Nat) (s : σ), f^[n * returnTime] (fiberBase s) =
      fiberBase (fiberNext^[n] s) := by
    intro n s
    induction n generalizing s with
    | zero => simp
    | succ n ih =>
        rw [Nat.succ_mul, Function.iterate_add_apply]
        rw [hreturn]
        rw [ih]
        rw [← Function.iterate_succ_apply]
  refine ⟨hf, ?_⟩
  intro x y
  rcases hbase.2 (proj x) b₀ with ⟨nx, hnx⟩
  have hxbase : proj (f^[nx] x) = b₀ := by
    rw [hcomm_iter, hnx]
  rcases hfiber_surj (f^[nx] x) hxbase with ⟨sx, hsx⟩
  rcases hbase.2 b₀ (proj y) with ⟨ny, hny⟩
  rcases (Function.Surjective.iterate hf.2 ny) y with ⟨y₀, hy₀⟩
  have hy₀base : proj y₀ = b₀ := by
    apply (Function.Injective.iterate hbase.1.1 ny)
    rw [← hcomm_iter, hy₀, hny]
  rcases hfiber_surj y₀ hy₀base with ⟨sy, hsy⟩
  rcases hfiber.2 sx sy with ⟨r, hr⟩
  refine ⟨ny + (r * returnTime + nx), ?_⟩
  calc
    f^[ny + (r * returnTime + nx)] x = f^[ny] (f^[r * returnTime + nx] x) := by
      rw [Function.iterate_add_apply]
    _ = f^[ny] (f^[r * returnTime] (f^[nx] x)) := by
      rw [Function.iterate_add_apply]
    _ = f^[ny] (f^[r * returnTime] (fiberBase sx)) := by rw [hsx]
    _ = f^[ny] (fiberBase (fiberNext^[r] sx)) := by rw [hreturn_iter]
    _ = f^[ny] (fiberBase sy) := by rw [hr]
    _ = f^[ny] y₀ := by rw [hsy]
    _ = y := hy₀

theorem foldl_bijective_of_forall_mem {α β : Type*}
    (L : List β) (F : β → α → α)
    (h : ∀ b, b ∈ L → Function.Bijective (F b)) :
    Function.Bijective (fun x => L.foldl (fun x b => F b x) x) := by
  induction L with
  | nil =>
      simpa using (Function.bijective_id : Function.Bijective (fun x : α => x))
  | cons b L ih =>
      simp only [List.mem_cons] at h
      change Function.Bijective ((fun x => L.foldl (fun x b => F b x) x) ∘ F b)
      exact Function.Bijective.comp
        (ih (by intro b' hb'; exact h b' (Or.inr hb')))
        (h b (Or.inl rfl))

theorem bijective_of_bijective_semiconj
    {α β : Type*} (f : α → α) (g : β → β) (φ : α → β)
    (hφ : Function.Bijective φ)
    (hcomm : ∀ x : α, φ (f x) = g (φ x))
    (hf : Function.Bijective f) :
    Function.Bijective g := by
  have hg_inj : Function.Injective g := by
    intro y₁ y₂ hy
    rcases hφ.2 y₁ with ⟨x₁, rfl⟩
    rcases hφ.2 y₂ with ⟨x₂, rfl⟩
    rw [← hcomm x₁, ← hcomm x₂] at hy
    exact congrArg φ (hf.1 (hφ.1 hy))
  have hg_surj : Function.Surjective g := by
    intro y
    rcases hφ.2 y with ⟨x, rfl⟩
    rcases hf.2 x with ⟨x₀, hx₀⟩
    refine ⟨φ x₀, ?_⟩
    rw [← hcomm, hx₀]
  exact ⟨hg_inj, hg_surj⟩

theorem zmod_rank_bijective_of_inverse
    {α : Type*} {N : Nat} [NeZero N]
    (rank : α → ZMod N) (inv : ZMod N → α)
    (hleft : ∀ x : α, inv (rank x) = x)
    (hright : ∀ r : ZMod N, rank (inv r) = r) :
    Function.Bijective rank :=
  bijective_of_inverse rank inv hleft hright

structure RankArrayCert (N : Nat) where
  next : Array Nat
  rank : Array Nat
  invRank : Array Nat

namespace RankArrayCert

def allUpTo (N : Nat) (p : Nat → Bool) : Bool :=
  (List.range N).all p

theorem allUpTo_true {N : Nat} {p : Nat → Bool}
    (h : allUpTo N p = true) {i : Nat} (hi : i < N) : p i = true := by
  exact (List.all_eq_true.mp h) i (List.mem_range.mpr hi)

def valuesLt (N : Nat) (a : Array Nat) : Bool :=
  allUpTo N fun i => decide (a.getD i 0 < N)

theorem valuesLt_true {N : Nat} {a : Array Nat}
    (h : valuesLt N a = true) :
    ∀ i : Fin N, a.getD i.val 0 < N := by
  intro i
  exact of_decide_eq_true (allUpTo_true h i.isLt)

def leftInvOk {N : Nat} (C : RankArrayCert N) : Bool :=
  allUpTo N fun i => decide (C.invRank.getD (C.rank.getD i 0) 0 = i)

def rightInvOk {N : Nat} (C : RankArrayCert N) : Bool :=
  allUpTo N fun r => decide (C.rank.getD (C.invRank.getD r 0) 0 = r)

def stepOk {N : Nat} (C : RankArrayCert N) : Bool :=
  allUpTo N fun i =>
    decide (C.rank.getD (C.next.getD i 0) 0 = (C.rank.getD i 0 + 1) % N)

theorem leftInvOk_true {N : Nat} {C : RankArrayCert N}
    (h : C.leftInvOk = true) :
    ∀ i : Fin N, C.invRank.getD (C.rank.getD i.val 0) 0 = i.val := by
  intro i
  exact of_decide_eq_true (allUpTo_true h i.isLt)

theorem rightInvOk_true {N : Nat} {C : RankArrayCert N}
    (h : C.rightInvOk = true) :
    ∀ r : Fin N, C.rank.getD (C.invRank.getD r.val 0) 0 = r.val := by
  intro r
  exact of_decide_eq_true (allUpTo_true h r.isLt)

theorem stepOk_true {N : Nat} {C : RankArrayCert N}
    (h : C.stepOk = true) :
    ∀ i : Fin N,
      C.rank.getD (C.next.getD i.val 0) 0 = (C.rank.getD i.val 0 + 1) % N := by
  intro i
  exact of_decide_eq_true (allUpTo_true h i.isLt)

def okParts {N : Nat} (C : RankArrayCert N) : List Bool :=
  [ decide (C.next.size = N)
  , decide (C.rank.size = N)
  , decide (C.invRank.size = N)
  , valuesLt N C.next
  , valuesLt N C.rank
  , valuesLt N C.invRank
  , leftInvOk C
  , rightInvOk C
  , stepOk C
  ]

def ok {N : Nat} (C : RankArrayCert N) : Bool :=
  C.okParts.all id

structure Valid {N : Nat} (C : RankArrayCert N) : Prop where
  next_size : C.next.size = N
  rank_size : C.rank.size = N
  invRank_size : C.invRank.size = N
  next_lt : ∀ i : Fin N, C.next.getD i.val 0 < N
  rank_lt : ∀ i : Fin N, C.rank.getD i.val 0 < N
  invRank_lt : ∀ r : Fin N, C.invRank.getD r.val 0 < N
  leftInv_val : ∀ i : Fin N, C.invRank.getD (C.rank.getD i.val 0) 0 = i.val
  rightInv_val : ∀ r : Fin N, C.rank.getD (C.invRank.getD r.val 0) 0 = r.val
  step_val : ∀ i : Fin N,
    C.rank.getD (C.next.getD i.val 0) 0 = (C.rank.getD i.val 0 + 1) % N

def nextFun {N : Nat} (C : RankArrayCert N) (h : C.Valid) : Fin N → Fin N :=
  fun i => ⟨C.next.getD i.val 0, h.next_lt i⟩

def rankFun {N : Nat} (C : RankArrayCert N) (h : C.Valid) : Fin N → Fin N :=
  fun i => ⟨C.rank.getD i.val 0, h.rank_lt i⟩

def invRankFun {N : Nat} (C : RankArrayCert N) (h : C.Valid) : Fin N → Fin N :=
  fun r => ⟨C.invRank.getD r.val 0, h.invRank_lt r⟩

theorem rankFun_left_inv {N : Nat} (C : RankArrayCert N) (h : C.Valid) :
    ∀ i : Fin N, C.invRankFun h (C.rankFun h i) = i := by
  intro i
  apply Fin.ext
  change C.invRank.getD (C.rank.getD i.val 0) 0 = i.val
  exact h.leftInv_val i

theorem rankFun_right_inv {N : Nat} (C : RankArrayCert N) (h : C.Valid) :
    ∀ r : Fin N, C.rankFun h (C.invRankFun h r) = r := by
  intro r
  apply Fin.ext
  change C.rank.getD (C.invRank.getD r.val 0) 0 = r.val
  exact h.rightInv_val r

theorem rankFun_step {N : Nat} [NeZero N] (C : RankArrayCert N) (h : C.Valid) :
    ∀ i : Fin N, C.rankFun h (C.nextFun h i) = C.rankFun h i + 1 := by
  intro i
  apply Fin.ext
  dsimp [nextFun, rankFun]
  rw [Fin.val_add]
  simpa using h.step_val i

theorem singleCycle_of_valid {N : Nat} [NeZero N]
    (C : RankArrayCert N) (h : C.Valid) :
    IsSingleCycleMap (C.nextFun h) := by
  exact singleCycle_of_rankFun
    (next := C.nextFun h)
    (rank := C.rankFun h)
    (bijective_of_inverse (C.rankFun h) (C.invRankFun h)
      (C.rankFun_left_inv h) (C.rankFun_right_inv h))
    (C.rankFun_step h)

theorem valid_of_ok {N : Nat} (C : RankArrayCert N) (h : C.ok = true) :
    C.Valid := by
  have hparts : ∀ b ∈ C.okParts, id b = true := by
    exact List.all_eq_true.mp (by simpa [ok] using h)
  have hNextSizeBool : decide (C.next.size = N) = true := by
    simpa using hparts (decide (C.next.size = N)) (by simp [okParts])
  have hRankSizeBool : decide (C.rank.size = N) = true := by
    simpa using hparts (decide (C.rank.size = N)) (by simp [okParts])
  have hInvRankSizeBool : decide (C.invRank.size = N) = true := by
    simpa using hparts (decide (C.invRank.size = N)) (by simp [okParts])
  have hNextLtBool : valuesLt N C.next = true := by
    simpa using hparts (valuesLt N C.next) (by simp [okParts])
  have hRankLtBool : valuesLt N C.rank = true := by
    simpa using hparts (valuesLt N C.rank) (by simp [okParts])
  have hInvRankLtBool : valuesLt N C.invRank = true := by
    simpa using hparts (valuesLt N C.invRank) (by simp [okParts])
  have hLeftInvBool : C.leftInvOk = true := by
    simpa using hparts C.leftInvOk (by simp [okParts])
  have hRightInvBool : C.rightInvOk = true := by
    simpa using hparts C.rightInvOk (by simp [okParts])
  have hStepBool : C.stepOk = true := by
    simpa using hparts C.stepOk (by simp [okParts])
  exact
    { next_size := of_decide_eq_true hNextSizeBool
      rank_size := of_decide_eq_true hRankSizeBool
      invRank_size := of_decide_eq_true hInvRankSizeBool
      next_lt := valuesLt_true hNextLtBool
      rank_lt := valuesLt_true hRankLtBool
      invRank_lt := valuesLt_true hInvRankLtBool
      leftInv_val := leftInvOk_true hLeftInvBool
      rightInv_val := rightInvOk_true hRightInvBool
      step_val := stepOk_true hStepBool }

def nextFunOfOk {N : Nat} (C : RankArrayCert N) (h : C.ok = true) : Fin N → Fin N :=
  C.nextFun (valid_of_ok C h)

theorem singleCycle_of_ok {N : Nat} [NeZero N]
    (C : RankArrayCert N) (h : C.ok = true) :
    IsSingleCycleMap (C.nextFunOfOk h) :=
  singleCycle_of_valid C (valid_of_ok C h)

end RankArrayCert

structure FinMapArrayCert (N : Nat) where
  map : Array Nat
  inv : Array Nat

namespace FinMapArrayCert

structure Valid {N : Nat} (C : FinMapArrayCert N) : Prop where
  map_size : C.map.size = N
  inv_size : C.inv.size = N
  map_lt : ∀ i : Fin N, C.map.getD i.val 0 < N
  inv_lt : ∀ i : Fin N, C.inv.getD i.val 0 < N
  leftInv_val : ∀ i : Fin N, C.inv.getD (C.map.getD i.val 0) 0 = i.val
  rightInv_val : ∀ i : Fin N, C.map.getD (C.inv.getD i.val 0) 0 = i.val

def mapFun {N : Nat} (C : FinMapArrayCert N) (h : C.Valid) : Fin N → Fin N :=
  fun i => ⟨C.map.getD i.val 0, h.map_lt i⟩

def invFun {N : Nat} (C : FinMapArrayCert N) (h : C.Valid) : Fin N → Fin N :=
  fun i => ⟨C.inv.getD i.val 0, h.inv_lt i⟩

theorem mapFun_left_inv {N : Nat} (C : FinMapArrayCert N) (h : C.Valid) :
    ∀ i : Fin N, C.invFun h (C.mapFun h i) = i := by
  intro i
  apply Fin.ext
  change C.inv.getD (C.map.getD i.val 0) 0 = i.val
  exact h.leftInv_val i

theorem mapFun_right_inv {N : Nat} (C : FinMapArrayCert N) (h : C.Valid) :
    ∀ i : Fin N, C.mapFun h (C.invFun h i) = i := by
  intro i
  apply Fin.ext
  change C.map.getD (C.inv.getD i.val 0) 0 = i.val
  exact h.rightInv_val i

theorem bijective_of_valid {N : Nat} (C : FinMapArrayCert N) (h : C.Valid) :
    Function.Bijective (C.mapFun h) :=
  bijective_of_inverse (C.mapFun h) (C.invFun h)
    (C.mapFun_left_inv h) (C.mapFun_right_inv h)

def leftInvOk {N : Nat} (C : FinMapArrayCert N) : Bool :=
  RankArrayCert.allUpTo N fun i => decide (C.inv.getD (C.map.getD i 0) 0 = i)

def rightInvOk {N : Nat} (C : FinMapArrayCert N) : Bool :=
  RankArrayCert.allUpTo N fun i => decide (C.map.getD (C.inv.getD i 0) 0 = i)

theorem leftInvOk_true {N : Nat} {C : FinMapArrayCert N}
    (h : C.leftInvOk = true) :
    ∀ i : Fin N, C.inv.getD (C.map.getD i.val 0) 0 = i.val := by
  intro i
  exact of_decide_eq_true (RankArrayCert.allUpTo_true h i.isLt)

theorem rightInvOk_true {N : Nat} {C : FinMapArrayCert N}
    (h : C.rightInvOk = true) :
    ∀ i : Fin N, C.map.getD (C.inv.getD i.val 0) 0 = i.val := by
  intro i
  exact of_decide_eq_true (RankArrayCert.allUpTo_true h i.isLt)

def okParts {N : Nat} (C : FinMapArrayCert N) : List Bool :=
  [ decide (C.map.size = N)
  , decide (C.inv.size = N)
  , RankArrayCert.valuesLt N C.map
  , RankArrayCert.valuesLt N C.inv
  , leftInvOk C
  , rightInvOk C
  ]

def ok {N : Nat} (C : FinMapArrayCert N) : Bool :=
  C.okParts.all id

theorem valid_of_ok {N : Nat} (C : FinMapArrayCert N) (h : C.ok = true) :
    C.Valid := by
  have hparts : ∀ b ∈ C.okParts, id b = true := by
    exact List.all_eq_true.mp (by simpa [ok] using h)
  have hMapSizeBool : decide (C.map.size = N) = true := by
    simpa using hparts (decide (C.map.size = N)) (by simp [okParts])
  have hInvSizeBool : decide (C.inv.size = N) = true := by
    simpa using hparts (decide (C.inv.size = N)) (by simp [okParts])
  have hMapLtBool : RankArrayCert.valuesLt N C.map = true := by
    simpa using hparts (RankArrayCert.valuesLt N C.map) (by simp [okParts])
  have hInvLtBool : RankArrayCert.valuesLt N C.inv = true := by
    simpa using hparts (RankArrayCert.valuesLt N C.inv) (by simp [okParts])
  have hLeftInvBool : C.leftInvOk = true := by
    simpa using hparts C.leftInvOk (by simp [okParts])
  have hRightInvBool : C.rightInvOk = true := by
    simpa using hparts C.rightInvOk (by simp [okParts])
  exact
    { map_size := of_decide_eq_true hMapSizeBool
      inv_size := of_decide_eq_true hInvSizeBool
      map_lt := RankArrayCert.valuesLt_true hMapLtBool
      inv_lt := RankArrayCert.valuesLt_true hInvLtBool
      leftInv_val := leftInvOk_true hLeftInvBool
      rightInv_val := rightInvOk_true hRightInvBool }

def mapFunOfOk {N : Nat} (C : FinMapArrayCert N) (h : C.ok = true) : Fin N → Fin N :=
  C.mapFun (valid_of_ok C h)

theorem bijective_of_ok {N : Nat} (C : FinMapArrayCert N) (h : C.ok = true) :
    Function.Bijective (C.mapFunOfOk h) :=
  bijective_of_valid C (valid_of_ok C h)

end FinMapArrayCert

end Handoff
end D7Odd
