import D5Odd.Matching
import Shared.TorusCayley

namespace D5Odd

def IsSingleCycleMapFinite {alpha : Type*} [Fintype alpha] (f : alpha -> alpha) : Prop :=
  Function.Bijective f ∧
    forall x y : alpha, ∃ n : Fin (Fintype.card alpha), f^[n.val] x = y

instance {alpha : Type*} [Fintype alpha] [DecidableEq alpha] (f : alpha -> alpha) :
    Decidable (IsSingleCycleMapFinite f) := by
  unfold IsSingleCycleMapFinite
  infer_instance

theorem IsSingleCycleMapFinite.toIsSingleCycleMap
    {alpha : Type*} [Fintype alpha] (f : alpha -> alpha)
    (h : IsSingleCycleMapFinite f) :
    IsSingleCycleMap f := by
  refine ⟨h.1, ?_⟩
  intro x y
  rcases h.2 x y with ⟨n, hn⟩
  exact ⟨n.1, hn⟩

def fin81AddNat (i : Fin 81) (k : Nat) : Fin 81 :=
  ⟨(i.val + k) % 81, Nat.mod_lt _ (by decide)⟩

@[simp] theorem fin81AddNat_zero (i : Fin 81) :
    fin81AddNat i 0 = i := by
  ext
  simp [fin81AddNat]

theorem fin81AddNat_add (i : Fin 81) (a b : Nat) :
    fin81AddNat (fin81AddNat i a) b = fin81AddNat i (a + b) := by
  ext
  simp [fin81AddNat]
  omega

theorem fin81AddNat_one_zmod (i : Fin 81) :
    (ZMod.finEquiv 81) (fin81AddNat i 1) =
      (ZMod.finEquiv 81) i + 1 := by
  apply ZMod.val_injective 81
  change (fin81AddNat i 1).val = (i + 1 : Fin 81).val
  simp [fin81AddNat, Fin.val_add]

set_option linter.style.nativeDecide false in
theorem fin81AddNat_one_bijective :
    Function.Bijective fun r : Fin 81 => fin81AddNat r 1 := by
  native_decide

set_option linter.style.nativeDecide false in
theorem fin81AddNat_reaches :
    ∀ i j : Fin 81, ∃ n : Fin 81, fin81AddNat i n.val = j := by
  native_decide

theorem single_cycle_of_rank
    {alpha : Type*} (f : alpha -> alpha) (rank : alpha -> Fin 81)
    (hrank : Function.Bijective rank)
    (hstep : ∀ x : alpha, rank (f x) = fin81AddNat (rank x) 1)
    (horbit : ∀ (x : alpha) (n : Fin 81), rank (f^[n.val] x) = fin81AddNat (rank x) n.val) :
    IsSingleCycleMap f := by
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply hrank.1
    have h : fin81AddNat (rank x) 1 = fin81AddNat (rank y) 1 := by
      simpa [hstep x, hstep y] using congrArg rank hxy
    exact fin81AddNat_one_bijective.1 h
  have hf_surj : Function.Surjective f := by
    intro y
    rcases fin81AddNat_one_bijective.2 (rank y) with ⟨r, hr⟩
    rcases hrank.2 r with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply hrank.1
    calc
      rank (f x) = fin81AddNat (rank x) 1 := hstep x
      _ = fin81AddNat r 1 := by rw [hx]
      _ = rank y := hr
  refine ⟨⟨hf_inj, hf_surj⟩, ?_⟩
  intro x y
  rcases fin81AddNat_reaches (rank x) (rank y) with ⟨n, hn⟩
  refine ⟨n.val, ?_⟩
  apply hrank.1
  calc
    rank (f^[n.val] x) = fin81AddNat (rank x) n.val := horbit x n
    _ = rank y := hn

theorem single_cycle_of_bijective_semiconj
    {alpha beta : Type*} (f : alpha -> alpha) (g : beta -> beta) (phi : alpha -> beta)
    (hphi : Function.Bijective phi)
    (hcomm : forall x : alpha, phi (f x) = g (phi x))
    (hf : IsSingleCycleMap f) :
    IsSingleCycleMap g := by
  have hcomm_iter : forall (n : Nat) (x : alpha), phi (f^[n] x) = g^[n] (phi x) := by
    intro n x
    induction n generalizing x with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hcomm, ih]
  refine ⟨?_, ?_⟩
  · constructor
    · intro y1 y2 hy
      rcases hphi.2 y1 with ⟨x1, rfl⟩
      rcases hphi.2 y2 with ⟨x2, rfl⟩
      apply congrArg phi
      apply hf.1.1
      apply hphi.1
      simpa [hcomm] using hy
    · intro y
      rcases hphi.2 y with ⟨x, rfl⟩
      rcases hf.1.2 x with ⟨x0, hx0⟩
      exact ⟨phi x0, by rw [← hcomm, hx0]⟩
  · intro y1 y2
    rcases hphi.2 y1 with ⟨x1, rfl⟩
    rcases hphi.2 y2 with ⟨x2, rfl⟩
    rcases hf.2 x1 x2 with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← hcomm_iter, hn]

theorem finRotate_single_cycle (n : Nat) :
    IsSingleCycleMap (finRotate n) := by
  refine ⟨(finRotate n).bijective, ?_⟩
  intro i j
  let k : Fin n := j - i
  refine ⟨k.val, ?_⟩
  change ((finRotate n)^[k.val]) i = j
  rw [← finCycle_eq_finRotate_iterate (k := k)]
  change i + (j - i) = j
  haveI := i.neZero
  abel

theorem finRotate_iterate_val {n : Nat} [NeZero n] (i : Fin n) (k : Nat) :
    (((finRotate n)^[k]) i).val = (i.val + k) % n := by
  induction k with
  | zero =>
      simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
      rw [Function.iterate_succ_apply', finRotate_apply, Fin.val_add, ih]
      rw [Fin.coe_ofNat_eq_mod]
      rw [← Nat.add_mod]
      rw [show i.val + k + 1 = i.val + (k + 1) by omega]

theorem finRotate_iterate_card {n : Nat} [NeZero n] (i : Fin n) :
    ((finRotate n)^[n]) i = i := by
  apply Fin.ext
  rw [finRotate_iterate_val]
  rw [Nat.add_mod_right]
  exact Nat.mod_eq_of_lt i.isLt

theorem finRotate_of_lt {n : Nat} [NeZero n] (i : Fin n)
    (h : i.val + 1 < n) :
    (finRotate n) i = ⟨i.val + 1, h⟩ := by
  rw [finRotate_apply]
  apply Fin.ext
  rw [Fin.val_add]
  have hgt1 : 1 < n := by omega
  have hone : ((1 : Fin n).val) = 1 := by
    rw [Fin.coe_ofNat_eq_mod]
    exact Nat.mod_eq_of_lt hgt1
  rw [hone]
  rw [Nat.mod_eq_of_lt h]

theorem finRotate_of_last {n : Nat} [NeZero n] (i : Fin n)
    (h : i.val + 1 = n) :
    (finRotate n) i = ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ := by
  rw [finRotate_apply]
  apply Fin.ext
  rw [Fin.val_add]
  by_cases hn1 : n = 1
  · subst n
    fin_cases i
    simp
  · have hgt1 : 1 < n := by
      have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
      omega
    rw [Fin.coe_ofNat_eq_mod]
    rw [Nat.mod_eq_of_lt hgt1]
    rw [h]
    simp

abbrev SigmaIdx (m : Nat) := Fin (m - 1) × Fin m

def sigmaIdxRank {m : Nat} : SigmaIdx m -> Fin ((m - 1) * m) :=
  finProdFinEquiv

def sigmaIdxSucc {m : Nat} (I : SigmaIdx m) : SigmaIdx m :=
  (finProdFinEquiv.symm ((finRotate ((m - 1) * m)) (sigmaIdxRank I)) :
    Fin (m - 1) × Fin m)

theorem sigmaIdxRank_sigmaIdxSucc {m : Nat} (I : SigmaIdx m) :
    sigmaIdxRank (sigmaIdxSucc I) =
      (finRotate ((m - 1) * m)) (sigmaIdxRank I) := by
  change finProdFinEquiv
      (finProdFinEquiv.symm ((finRotate ((m - 1) * m)) (sigmaIdxRank I))) =
    (finRotate ((m - 1) * m)) (sigmaIdxRank I)
  exact Equiv.apply_symm_apply finProdFinEquiv _

theorem sigmaIdxSucc_single_cycle {m : Nat} :
    IsSingleCycleMap (sigmaIdxSucc (m := m)) := by
  exact single_cycle_of_bijective_semiconj
    (f := finRotate ((m - 1) * m))
    (g := sigmaIdxSucc (m := m))
    (phi := (finProdFinEquiv.symm :
      Fin ((m - 1) * m) -> SigmaIdx m))
    (Equiv.bijective finProdFinEquiv.symm)
    (by
      intro x
      change finProdFinEquiv.symm ((finRotate ((m - 1) * m)) x) =
        finProdFinEquiv.symm
          ((finRotate ((m - 1) * m))
            (finProdFinEquiv (finProdFinEquiv.symm x)))
      rw [Equiv.apply_symm_apply])
    (finRotate_single_cycle ((m - 1) * m))

theorem sigmaIdxSucc_of_col_lt {m : Nat} (I : SigmaIdx m)
    (hcol : I.2.val + 1 < m) :
    sigmaIdxSucc I = (I.1, ⟨I.2.val + 1, hcol⟩) := by
  apply (Equiv.injective finProdFinEquiv)
  change sigmaIdxRank (sigmaIdxSucc I) =
    sigmaIdxRank (I.1, ⟨I.2.val + 1, hcol⟩)
  rw [sigmaIdxRank_sigmaIdxSucc, finRotate_apply]
  apply Fin.ext
  rw [Fin.val_add]
  have hNpos : 0 < (m - 1) * m := Fin.pos_iff_nonempty.2 ⟨sigmaIdxRank I⟩
  haveI : NeZero ((m - 1) * m) := ⟨Nat.ne_of_gt hNpos⟩
  have hNgt1 : 1 < (m - 1) * m := by
    have hmpos : 0 < m := by omega
    have hm1pos : 0 < m - 1 := Fin.pos_iff_nonempty.2 ⟨I.1⟩
    nlinarith [Nat.mul_pos hm1pos hmpos]
  have hone : ((1 : Fin ((m - 1) * m)).val) = 1 := by
    rw [Fin.coe_ofNat_eq_mod]
    exact Nat.mod_eq_of_lt hNgt1
  rw [hone]
  have hlt : (sigmaIdxRank I).val + 1 < (m - 1) * m := by
    have hrowSucc : I.1.val + 1 <= m - 1 := Nat.succ_le_of_lt I.1.isLt
    calc
      (sigmaIdxRank I).val + 1 = I.2.val + m * I.1.val + 1 := by
        simp [sigmaIdxRank, finProdFinEquiv]
      _ = (I.2.val + 1) + m * I.1.val := by omega
      _ < m + m * I.1.val := Nat.add_lt_add_right hcol _
      _ = m * (I.1.val + 1) := by rw [Nat.mul_succ, add_comm]
      _ <= m * (m - 1) := Nat.mul_le_mul_left m hrowSucc
      _ = (m - 1) * m := by rw [Nat.mul_comm]
  rw [Nat.mod_eq_of_lt hlt]
  simp [sigmaIdxRank, finProdFinEquiv]
  omega

theorem sigmaIdxSucc_of_last_col_row_lt {m : Nat} (I : SigmaIdx m)
    (hcol : I.2.val + 1 = m) (hrow : I.1.val + 1 < m - 1) :
    sigmaIdxSucc I = (⟨I.1.val + 1, hrow⟩, (⟨0, by omega⟩ : Fin m)) := by
  apply (Equiv.injective finProdFinEquiv)
  change sigmaIdxRank (sigmaIdxSucc I) =
    sigmaIdxRank (⟨I.1.val + 1, hrow⟩, (⟨0, by omega⟩ : Fin m))
  rw [sigmaIdxRank_sigmaIdxSucc, finRotate_apply]
  apply Fin.ext
  rw [Fin.val_add]
  have hNpos : 0 < (m - 1) * m := Fin.pos_iff_nonempty.2 ⟨sigmaIdxRank I⟩
  haveI : NeZero ((m - 1) * m) := ⟨Nat.ne_of_gt hNpos⟩
  have hNgt1 : 1 < (m - 1) * m := by
    have hmge2 : 2 <= m := by omega
    have hm1ge1 : 1 <= m - 1 := by omega
    exact lt_of_lt_of_le (by omega) (Nat.mul_le_mul hm1ge1 hmge2)
  have hone : ((1 : Fin ((m - 1) * m)).val) = 1 := by
    rw [Fin.coe_ofNat_eq_mod]
    exact Nat.mod_eq_of_lt hNgt1
  rw [hone]
  have hlt : (sigmaIdxRank I).val + 1 < (m - 1) * m := by
    calc
      (sigmaIdxRank I).val + 1 = I.2.val + m * I.1.val + 1 := by
        simp [sigmaIdxRank, finProdFinEquiv]
      _ = m * (I.1.val + 1) := by
        rw [Nat.mul_succ]
        omega
      _ < m * (m - 1) := by
        apply Nat.mul_lt_mul_of_pos_left hrow
        omega
      _ = (m - 1) * m := by rw [Nat.mul_comm]
  rw [Nat.mod_eq_of_lt hlt]
  simp [sigmaIdxRank, finProdFinEquiv]
  rw [Nat.mul_succ]
  omega

theorem sigmaIdxSucc_of_last {m : Nat} (I : SigmaIdx m)
    (hcol : I.2.val + 1 = m) (hrow : I.1.val + 1 = m - 1) :
    sigmaIdxSucc I = ((⟨0, by omega⟩ : Fin (m - 1)), (⟨0, by omega⟩ : Fin m)) := by
  apply (Equiv.injective finProdFinEquiv)
  change sigmaIdxRank (sigmaIdxSucc I) =
    sigmaIdxRank ((⟨0, by omega⟩ : Fin (m - 1)), (⟨0, by omega⟩ : Fin m))
  rw [sigmaIdxRank_sigmaIdxSucc, finRotate_apply]
  apply Fin.ext
  rw [Fin.val_add]
  have hNpos : 0 < (m - 1) * m := Fin.pos_iff_nonempty.2 ⟨sigmaIdxRank I⟩
  haveI : NeZero ((m - 1) * m) := ⟨Nat.ne_of_gt hNpos⟩
  have hNgt1 : 1 < (m - 1) * m := by
    have hmge2 : 2 <= m := by omega
    have hm1ge1 : 1 <= m - 1 := by omega
    exact lt_of_lt_of_le (by omega) (Nat.mul_le_mul hm1ge1 hmge2)
  have hone : ((1 : Fin ((m - 1) * m)).val) = 1 := by
    rw [Fin.coe_ofNat_eq_mod]
    exact Nat.mod_eq_of_lt hNgt1
  rw [hone]
  have heqN : (sigmaIdxRank I).val + 1 = (m - 1) * m := by
    calc
      (sigmaIdxRank I).val + 1 = I.2.val + m * I.1.val + 1 := by
        simp [sigmaIdxRank, finProdFinEquiv]
      _ = m * (I.1.val + 1) := by
        rw [Nat.mul_succ]
        omega
      _ = m * (m - 1) := by rw [hrow]
      _ = (m - 1) * m := by rw [Nat.mul_comm]
  rw [heqN]
  simp [Nat.mod_self, sigmaIdxRank, finProdFinEquiv]


theorem single_cycle_of_return_cover
    {alpha sigma : Type*} (f : alpha -> alpha) (base : sigma -> alpha)
    (next : sigma -> sigma) (time : sigma -> Nat)
    (hf : Function.Bijective f)
    (hreturn : forall s : sigma, f^[time s] (base s) = base (next s))
    (hcover : forall x : alpha, exists s : sigma, exists k : Nat,
      k < time s ∧ f^[k] (base s) = x)
    (hnext : IsSingleCycleMap next) :
    IsSingleCycleMap f := by
  refine ⟨hf, ?_⟩
  have hbase : forall (s : sigma) (n : Nat),
      exists N : Nat, f^[N] (base s) = base (next^[n] s) := by
    intro s n
    induction n with
    | zero =>
        exact ⟨0, rfl⟩
    | succ n ih =>
        rcases ih with ⟨N, hN⟩
        let u : sigma := next^[n] s
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

abbrev ReturnSeg (sigma : Type*) (time : sigma -> Nat) :=
  Sigma fun s : sigma => Fin (time s)

def returnSegPoint {alpha sigma : Type*} (f : alpha -> alpha) (base : sigma -> alpha)
    (time : sigma -> Nat) (u : ReturnSeg sigma time) : alpha :=
  f^[u.2.val] (base u.1)

theorem returnSegPoint_injective
    {alpha sigma : Type*} [Fintype sigma]
    (f : alpha -> alpha) (base : sigma -> alpha) (time : sigma -> Nat)
    (hf : Function.Bijective f)
    (hbase_inj : Function.Injective base)
    (hfirst : forall s : sigma, forall k : Nat, 0 < k -> k < time s ->
      ¬ exists t : sigma, f^[k] (base s) = base t) :
    Function.Injective (returnSegPoint f base time) := by
  intro u v huv
  rcases u with ⟨su, ku⟩
  rcases v with ⟨sv, kv⟩
  dsimp [returnSegPoint] at huv
  by_cases hle : ku.val <= kv.val
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
  · have hle' : kv.val <= ku.val := by omega
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
    {alpha sigma : Type*} [Fintype alpha] [Fintype sigma]
    (f : alpha -> alpha) (base : sigma -> alpha) (time : sigma -> Nat)
    (hf : Function.Bijective f)
    (hbase_inj : Function.Injective base)
    (hfirst : forall s : sigma, forall k : Nat, 0 < k -> k < time s ->
      ¬ exists t : sigma, f^[k] (base s) = base t)
    (hsum : (Finset.univ.sum fun s : sigma => time s) = Fintype.card alpha) :
    Function.Bijective (returnSegPoint f base time) := by
  apply (Fintype.bijective_iff_injective_and_card
    (returnSegPoint f base time)).2
  refine ⟨returnSegPoint_injective f base time hf hbase_inj hfirst, ?_⟩
  calc
    Fintype.card (ReturnSeg sigma time) =
        Finset.univ.sum fun s : sigma => Fintype.card (Fin (time s)) := by
          simp [ReturnSeg, Fintype.card_sigma]
    _ = Finset.univ.sum fun s : sigma => time s := by
          simp
    _ = Fintype.card alpha := hsum

theorem return_cover_of_first_return_sum
    {alpha sigma : Type*} [Fintype alpha] [Fintype sigma]
    (f : alpha -> alpha) (base : sigma -> alpha) (time : sigma -> Nat)
    (hf : Function.Bijective f)
    (hbase_inj : Function.Injective base)
    (hfirst : forall s : sigma, forall k : Nat, 0 < k -> k < time s ->
      ¬ exists t : sigma, f^[k] (base s) = base t)
    (hsum : (Finset.univ.sum fun s : sigma => time s) = Fintype.card alpha) :
    forall x : alpha, exists s : sigma, exists k : Nat,
      k < time s ∧ f^[k] (base s) = x := by
  intro x
  rcases (returnSegPoint_bijective_of_first_return_sum
      f base time hf hbase_inj hfirst hsum).2 x with ⟨u, hu⟩
  exact ⟨u.1, u.2.val, u.2.isLt, hu⟩

theorem single_cycle_of_first_return_sum
    {alpha sigma : Type*} [Fintype alpha] [Fintype sigma]
    (f : alpha -> alpha) (base : sigma -> alpha)
    (next : sigma -> sigma) (time : sigma -> Nat)
    (hf : Function.Bijective f)
    (hbase_inj : Function.Injective base)
    (hreturn : forall s : sigma, f^[time s] (base s) = base (next s))
    (hfirst : forall s : sigma, forall k : Nat, 0 < k -> k < time s ->
      ¬ exists t : sigma, f^[k] (base s) = base t)
    (hnext : IsSingleCycleMap next)
    (hsum : (Finset.univ.sum fun s : sigma => time s) = Fintype.card alpha) :
    IsSingleCycleMap f := by
  exact single_cycle_of_return_cover f base next time hf hreturn
    (return_cover_of_first_return_sum f base time hf hbase_inj hfirst hsum)
    hnext

theorem root5_neg {m : Nat} {w : Vec5 m} (hw : Root5 m w) : Root5 m (-w) := by
  unfold Root5 at hw ⊢
  calc
    sum5 m (-w) = -sum5 m w := by simp [sum5, Finset.sum_neg_distrib]
    _ = 0 := by rw [hw]; simp

theorem root5_add_root {m : Nat} {x y : Vec5 m} (hx : Root5 m x) (hy : Root5 m y) :
    Root5 m (x + y) := by
  unfold Root5 at hx hy ⊢
  rw [sum5_add, hx, hy]
  simp

theorem root5_q5_vec (m : Nat) (i : Fin 5) : Root5 m (q5 m i) := by
  unfold Root5
  exact sum5_q5 m i

theorem root5_neg_q5_vec (m : Nat) (i : Fin 5) : Root5 m (-q5 m i) :=
  root5_neg (root5_q5_vec m i)

theorem root5_nsmul_root {m : Nat} (k : Nat) {r : Vec5 m} (hr : Root5 m r) :
    Root5 m (k • r) := by
  unfold Root5 sum5 at hr ⊢
  simp [nsmul_eq_mul]
  rw [← Finset.mul_sum]
  rw [hr, mul_zero]

theorem root5_four_eq_neg_sum4 {m : Nat} {w : Vec5 m} (hw : Root5 m w) :
    w 4 = -(w 0 + w 1 + w 2 + w 3) := by
  unfold Root5 sum5 at hw
  rw [Fin.sum_univ_five] at hw
  change w 0 + w 1 + w 2 + w 3 + w 4 = 0 at hw
  calc
    w 4 = (w 0 + w 1 + w 2 + w 3 + w 4) -
        (w 0 + w 1 + w 2 + w 3) := by abel
    _ = 0 - (w 0 + w 1 + w 2 + w 3) := by rw [hw]
    _ = -(w 0 + w 1 + w 2 + w 3) := by abel

def rootQuadVec {m : Nat} (x : Fin 4 -> ZMod m) : Vec5 m :=
  ![x 0, x 1, x 2, x 3, -(x 0 + x 1 + x 2 + x 3)]

theorem root5_rootQuadVec {m : Nat} (x : Fin 4 -> ZMod m) :
    Root5 m (rootQuadVec x) := by
  unfold Root5 sum5 rootQuadVec
  rw [Fin.sum_univ_five]
  simp

def rootOfQuad {m : Nat} (x : Fin 4 -> ZMod m) : ARoot5 m :=
  ⟨rootQuadVec x, root5_rootQuadVec x⟩

def quadOfRoot {m : Nat} (w : ARoot5 m) : Fin 4 -> ZMod m :=
  fun i => w.1 ⟨i.val, by omega⟩

theorem quadOfRoot_rootOfQuad {m : Nat} (x : Fin 4 -> ZMod m) :
    quadOfRoot (rootOfQuad x) = x := by
  funext i
  fin_cases i <;> simp [quadOfRoot, rootOfQuad, rootQuadVec]

theorem rootOfQuad_quadOfRoot {m : Nat} (w : ARoot5 m) :
    rootOfQuad (quadOfRoot w) = w := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [quadOfRoot, rootOfQuad, rootQuadVec]
  rw [root5_four_eq_neg_sum4 w.2]
  abel

def rootQuadEquiv (m : Nat) : (Fin 4 -> ZMod m) ≃ ARoot5 m where
  toFun := rootOfQuad
  invFun := quadOfRoot
  left_inv := quadOfRoot_rootOfQuad
  right_inv := rootOfQuad_quadOfRoot

theorem card_ARoot5 {m : Nat} [NeZero m] :
    Fintype.card (ARoot5 m) = m ^ 4 := by
  have hcard := Fintype.card_congr (rootQuadEquiv m)
  calc
    Fintype.card (ARoot5 m) = Fintype.card (Fin 4 -> ZMod m) := hcard.symm
    _ = Fintype.card (ZMod m) ^ 4 := by
      simpa using (Fintype.card_pi_const (ZMod m) 4)
    _ = m ^ 4 := by
      rw [ZMod.card]

def rootTranslate {m : Nat} (r : Vec5 m) (hr : Root5 m r) (w : ARoot5 m) : ARoot5 m :=
  ⟨w.1 + r, root5_add_root w.2 hr⟩

theorem rootTranslate_bijective {m : Nat} (r : Vec5 m) (hr : Root5 m r) :
    Function.Bijective (rootTranslate r hr) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    have h := congrArg Subtype.val hxy
    change x.1 + r = y.1 + r at h
    exact add_right_cancel h
  · intro y
    refine ⟨⟨y.1 - r, ?_⟩, ?_⟩
    · have hneg : Root5 m (-r) := root5_neg hr
      simpa [sub_eq_add_neg] using root5_add_root y.2 hneg
    · apply Subtype.ext
      simp [rootTranslate]

theorem rootTranslate_comp {m : Nat} (r s : Vec5 m)
    (hr : Root5 m r) (hs : Root5 m s) (w : ARoot5 m) :
    rootTranslate r hr (rootTranslate s hs w) =
      rootTranslate (s + r) (root5_add_root hs hr) w := by
  apply Subtype.ext
  simp [rootTranslate, add_assoc]

theorem rootTranslate_zero {m : Nat} (h0 : Root5 m (0 : Vec5 m)) (w : ARoot5 m) :
    rootTranslate (0 : Vec5 m) h0 w = w := by
  apply Subtype.ext
  simp [rootTranslate]

def fin5SubNat (i : Fin 5) (k : Nat) : Fin 5 :=
  fin5AddNat i (5 - k % 5)

def rotVec {m : Nat} (c : Color) (w : Vec5 m) : Vec5 m :=
  fun j => w (fin5SubNat j c.val)

theorem root5_rotVec {m : Nat} (c : Color) {w : Vec5 m} (hw : Root5 m w) :
    Root5 m (rotVec c w) := by
  unfold Root5 sum5 rotVec fin5SubNat fin5AddNat at *
  fin_cases c <;> simp [Fin.sum_univ_five] at * <;> abel_nf at * <;> assumption

def rootRotate {m : Nat} (c : Color) (w : ARoot5 m) : ARoot5 m :=
  ⟨rotVec c w.1, root5_rotVec c w.2⟩

theorem rootRotate_bijective {m : Nat} (c : Color) :
    Function.Bijective (rootRotate (m := m) c) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hv := congrArg Subtype.val hxy
    ext j
    have hj := congrFun hv (fin5AddNat j c.val)
    fin_cases c <;> fin_cases j <;>
      simpa [rootRotate, rotVec, fin5SubNat, fin5AddNat] using hj
  · intro y
    let cinv : Color := fin5SubNat 0 c.val
    refine ⟨rootRotate cinv y, ?_⟩
    apply Subtype.ext
    ext j
    fin_cases c <;> fin_cases j <;>
      simp [rootRotate, rotVec, cinv, fin5SubNat, fin5AddNat]

def rotMask (c : Color) (S : Mask5) : Mask5 :=
  fun j => S (fin5SubNat j c.val)

set_option linter.style.nativeDecide false in
theorem Lambda1_cyclic :
    forall (S : Mask5) (a c : Color),
      Lambda1 (rotMask c S) (fin5AddNat a c.val) =
        fin5AddNat (Lambda1 S a) c.val := by
  native_decide

def pc5 {m : Nat} (c : Color) (w : Vec5 m) : Direction :=
  Lambda1 (zeroMaskMinusOne w) c

def colorPc {m : Nat} (c : Color) (w : ARoot5 m) : ARoot5 m :=
  ⟨w.1 + q5 m (pc5 c w.1), root5_add_q5 w.2 _⟩

theorem zeroMaskMinusOne_rotVec {m : Nat} (c : Color) (w : Vec5 m) :
    zeroMaskMinusOne (rotVec c w) = rotMask c (zeroMaskMinusOne w) := by
  ext j
  unfold zeroMaskMinusOne zeroMask rotVec rotMask fin5SubNat fin5AddNat
  fin_cases c <;> fin_cases j <;> simp

theorem pc5_rotVec {m : Nat} (c : Color) (w : Vec5 m) :
    pc5 c (rotVec c w) = fin5AddNat (p5 w) c.val := by
  have hc0 : fin5AddNat 0 c.val = c := by
    ext
    simp [fin5AddNat]
  calc
    pc5 c (rotVec c w) = pc5 (fin5AddNat 0 c.val) (rotVec c w) := by rw [hc0]
    _ = fin5AddNat (p5 w) c.val := by
      rw [pc5, p5, zeroMaskMinusOne_rotVec]
      exact Lambda1_cyclic (zeroMaskMinusOne w) 0 c

theorem layerMap_ge5_regular {m : Nat} (t : Fin m) (c : Color)
    (h1 : t.val ≠ 1) (h2 : t.val ≠ 2) (h3 : t.val ≠ 3) (w : ARoot5 m) :
    layerMap (ge5Schedule m) t c w =
      rootTranslate (q5 m c) (root5_q5_vec m c) w := by
  apply Subtype.ext
  simp [layerMap, rootTranslate, ge5Schedule, ge5Dir, h1, h2, h3]

theorem layerMap_ge5_two {m : Nat} (t : Fin m) (c : Color) (ht : t.val = 2)
    (w : ARoot5 m) :
    layerMap (ge5Schedule m) t c w =
      rootTranslate (q5 m (fin5AddNat c 3)) (root5_q5_vec m (fin5AddNat c 3)) w := by
  apply Subtype.ext
  simp [layerMap, rootTranslate, ge5Schedule, ge5Dir, ht, fin5AddNat]

theorem layerMap_ge5_three {m : Nat} (t : Fin m) (c : Color) (ht : t.val = 3)
    (w : ARoot5 m) :
    layerMap (ge5Schedule m) t c w =
      rootTranslate (q5 m (fin5AddNat c 4)) (root5_q5_vec m (fin5AddNat c 4)) w := by
  apply Subtype.ext
  simp [layerMap, rootTranslate, ge5Schedule, ge5Dir, ht, fin5AddNat]

theorem fold_ge5_regular {m : Nat} (l : List (Fin m)) (c : Color)
    (hall : forall t : Fin m, t ∈ l -> t.val ≠ 1 ∧ t.val ≠ 2 ∧ t.val ≠ 3)
    (w : ARoot5 m) :
    l.foldl (fun x t => layerMap (ge5Schedule m) t c x) w =
      rootTranslate ((l.length : Nat) • q5 m c)
        (root5_nsmul_root l.length (root5_q5_vec m c)) w := by
  induction l generalizing w with
  | nil =>
      apply Subtype.ext
      simp [rootTranslate]
  | cons t l ih =>
      rw [List.foldl_cons]
      have ht := hall t (by simp)
      rw [layerMap_ge5_regular t c ht.1 ht.2.1 ht.2.2]
      have hall_tail : forall u : Fin m, u ∈ l -> u.val ≠ 1 ∧ u.val ≠ 2 ∧ u.val ≠ 3 := by
        intro u hu
        exact hall u (by simp [hu])
      rw [ih hall_tail]
      apply Subtype.ext
      ext i
      simp [rootTranslate, nsmul_eq_mul, Nat.cast_add]
      ring

theorem layerMap_ge5_color0_regular {m : Nat} (t : Fin m)
    (h1 : t.val ≠ 1) (h2 : t.val ≠ 2) (h3 : t.val ≠ 3) (w : ARoot5 m) :
    layerMap (ge5Schedule m) t 0 w =
      rootTranslate (q5 m 0) (root5_q5_vec m 0) w := by
  apply Subtype.ext
  simp [layerMap, rootTranslate, ge5Schedule, ge5Dir, h1, h2, h3]

theorem layerMap_ge5_color0_two {m : Nat} (t : Fin m) (ht : t.val = 2)
    (w : ARoot5 m) :
    layerMap (ge5Schedule m) t 0 w =
      rootTranslate (q5 m 3) (root5_q5_vec m 3) w := by
  apply Subtype.ext
  simp [layerMap, rootTranslate, ge5Schedule, ge5Dir, ht, fin5AddNat]

theorem layerMap_ge5_color0_three {m : Nat} (t : Fin m) (ht : t.val = 3)
    (w : ARoot5 m) :
    layerMap (ge5Schedule m) t 0 w =
      rootTranslate (q5 m 4) (root5_q5_vec m 4) w := by
  apply Subtype.ext
  simp [layerMap, rootTranslate, ge5Schedule, ge5Dir, ht, fin5AddNat]

theorem fold_ge5_color0_regular {m : Nat} (l : List (Fin m))
    (hall : forall t : Fin m, t ∈ l -> t.val ≠ 1 ∧ t.val ≠ 2 ∧ t.val ≠ 3)
    (w : ARoot5 m) :
    l.foldl (fun x t => layerMap (ge5Schedule m) t 0 x) w =
      rootTranslate ((l.length : Nat) • q5 m 0)
        (root5_nsmul_root l.length (root5_q5_vec m 0)) w := by
  induction l generalizing w with
  | nil =>
      apply Subtype.ext
      simp [rootTranslate]
  | cons t l ih =>
      rw [List.foldl_cons]
      have ht := hall t (by simp)
      rw [layerMap_ge5_color0_regular t ht.1 ht.2.1 ht.2.2]
      have hall_tail : forall u : Fin m, u ∈ l -> u.val ≠ 1 ∧ u.val ≠ 2 ∧ u.val ≠ 3 := by
        intro u hu
        exact hall u (by simp [hu])
      rw [ih hall_tail]
      apply Subtype.ext
      ext i
      simp [rootTranslate, nsmul_eq_mul, Nat.cast_add]
      ring

def finSucc4 {n : Nat} (t : Fin (n + 1)) : Fin (n + 5) :=
  Fin.succ (Fin.succ (Fin.succ (Fin.succ t)))

theorem zmod_nat_add_one_eq_neg_four (n : Nat) :
    ((n + 1 : Nat) : ZMod (n + 5)) = (-4 : ZMod (n + 5)) := by
  have h1 : ((n + 1 : Nat) : ZMod (n + 5)) + 4 = 0 := by
    change ((n + 1 : Nat) : ZMod (n + 5)) + ((4 : Nat) : ZMod (n + 5)) = 0
    rw [← Nat.cast_add]
    convert ZMod.natCast_self (n + 5) using 2
  linear_combination h1

def colorZeroP {m : Nat} (w : ARoot5 m) : ARoot5 m :=
  ⟨w.1 + q5 m (p5 w.1), root5_add_q5 w.2 _⟩

theorem colorZeroP_eq_layerMap_one {m : Nat} [NeZero m] (hm : 5 <= m) :
    (fun w : ARoot5 m => layerMap (ge5Schedule m) ⟨1, by omega⟩ 0 w) = colorZeroP := by
  funext w
  apply Subtype.ext
  simp [colorZeroP, layerMap, ge5Schedule, ge5Dir, p5]

theorem colorZeroP_bijective {m : Nat} [NeZero m] (hm : 5 <= m) :
    Function.Bijective (colorZeroP (m := m)) := by
  let t : Fin m := ⟨1, by omega⟩
  have h := layerMap_bijective_of_exactCover (ge5Schedule_exact (m := m) hm) t 0
  change Function.Bijective (fun w : ARoot5 m => layerMap (ge5Schedule m) t 0 w) at h
  rw [show (fun w : ARoot5 m => layerMap (ge5Schedule m) t 0 w) = colorZeroP by
    subst t
    exact colorZeroP_eq_layerMap_one hm] at h
  exact h

theorem zeroMaskMinusOne_eq_mask5 {m : Nat} (w : Vec5 m) :
    zeroMaskMinusOne w =
      mask5 (decide (w 1 = 0)) (decide (w 2 = 0)) (decide (w 3 = 0))
        (decide (w 4 = 0)) (decide (w 0 = 0)) := by
  ext j
  fin_cases j <;> simp [zeroMaskMinusOne, zeroMask, fin5AddNat, mask5]

@[simp] theorem vec5_get0 {m : Nat} (w : Vec5 m) : Matrix.vecHead w = w 0 := rfl

@[simp] theorem vec5_get1 {m : Nat} (w : Vec5 m) :
    Matrix.vecHead (Matrix.vecTail w) = w 1 := rfl

@[simp] theorem vec5_get2 {m : Nat} (w : Vec5 m) :
    Matrix.vecHead (Matrix.vecTail (Matrix.vecTail w)) = w 2 := rfl

@[simp] theorem vec5_get3 {m : Nat} (w : Vec5 m) :
    Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail w))) = w 3 := rfl

@[simp] theorem vec5_get4 {m : Nat} (w : Vec5 m) :
    Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail w)))) =
      w 4 := rfl

theorem p5_eq_two_iff_root {m : Nat} {w : Vec5 m} (hw : Root5 m w) :
    p5 w = 2 ↔ w 0 = 0 ∧ w 3 = 0 ∧ w 4 ≠ 0 := by
  rw [p5]
  rw [zeroMaskMinusOne_eq_mask5 w]
  by_cases h0 : w 0 = 0 <;> by_cases h1 : w 1 = 0 <;>
    by_cases h2 : w 2 = 0 <;> by_cases h3 : w 3 = 0 <;>
    by_cases h4 : w 4 = 0
  all_goals
    unfold Root5 sum5 at hw
    rw [Fin.sum_univ_five] at hw
    simp [Lambda1, mask5, row5, h0, h1, h2, h3, h4] at *

theorem p5_ne_two_of_root_guard {m : Nat} {w : Vec5 m}
    (hw : Root5 m w)
    (hguard : w 0 ≠ 0 ∨ w 3 ≠ 0 ∨ w 4 = 0) :
    p5 w ≠ 2 := by
  intro hp
  have h := (p5_eq_two_iff_root hw).1 hp
  rcases h with ⟨h0, h3, h4ne⟩
  rcases hguard with h0ne | h3ne | h4zero
  · exact h0ne h0
  · exact h3ne h3
  · exact h4ne h4zero

theorem p5_ne_two_of_three_ne_zero {m : Nat} {w : Vec5 m}
    (h3 : w 3 ≠ 0) :
    p5 w ≠ 2 := by
  rw [p5, zeroMaskMinusOne_eq_mask5]
  by_cases h0 : w 0 = 0 <;> by_cases h1 : w 1 = 0 <;>
    by_cases h2 : w 2 = 0 <;> by_cases h4 : w 4 = 0
  all_goals
    simp [Lambda1, mask5, row5, h0, h1, h2, h3, h4]

theorem p5_ne_two_of_four_zero {m : Nat} {w : Vec5 m}
    (h4 : w 4 = 0) :
    p5 w ≠ 2 := by
  rw [p5, zeroMaskMinusOne_eq_mask5]
  by_cases h0 : w 0 = 0 <;> by_cases h1 : w 1 = 0 <;>
    by_cases h2 : w 2 = 0 <;> by_cases h3 : w 3 = 0
  all_goals
    simp [Lambda1, mask5, row5, h0, h1, h2, h3, h4]

def sigmaVec {m : Nat} (a b : ZMod m) : Vec5 m :=
  ![0, a, b, 0, -a - b]

def EVec {m : Nat} (u v : ZMod m) : Vec5 m :=
  ![u, v, 0, 0, -u - v]

theorem root5_sigmaVec {m : Nat} (a b : ZMod m) : Root5 m (sigmaVec a b) := by
  unfold Root5 sum5 sigmaVec
  rw [Fin.sum_univ_five]
  simp

@[simp] theorem root5_EVec {m : Nat} (u v : ZMod m) :
    Root5 m (EVec u v) := by
  unfold Root5 sum5 EVec
  rw [Fin.sum_univ_five]
  simp

@[simp] theorem EVec_zero_left_eq_sigmaVec {m : Nat} (v : ZMod m) :
    EVec 0 v = sigmaVec v 0 := by
  ext i
  fin_cases i <;> simp [EVec, sigmaVec]

theorem p5_sigmaVec_eq_two_iff {m : Nat} (a b : ZMod m) :
    p5 (sigmaVec a b) = 2 ↔ a + b ≠ 0 := by
  rw [p5_eq_two_iff_root (root5_sigmaVec a b)]
  change ((0 : ZMod m) = 0 ∧ (0 : ZMod m) = 0 ∧ (-a - b : ZMod m) ≠ 0) ↔
    a + b ≠ 0
  simp only [true_and]
  rw [show (-a - b : ZMod m) = -(a + b) by abel]
  exact neg_ne_zero

theorem root5_four_eq_neg_add_of_zero_zero {m : Nat} {w : Vec5 m}
    (hw : Root5 m w) (h0 : w 0 = 0) (h3 : w 3 = 0) :
    w 4 = -w 1 - w 2 := by
  unfold Root5 sum5 at hw
  rw [Fin.sum_univ_five] at hw
  change w 0 + w 1 + w 2 + w 3 + w 4 = 0 at hw
  rw [h0, h3] at hw
  simp only [zero_add, add_zero] at hw
  calc
    w 4 = w 1 + w 2 + w 4 - (w 1 + w 2) := by abel
    _ = 0 - (w 1 + w 2) := by rw [hw]
    _ = -w 1 - w 2 := by abel

theorem eq_sigmaVec_of_p5_eq_two {m : Nat} {w : Vec5 m}
    (hw : Root5 m w) (hp : p5 w = 2) :
    w = sigmaVec (w 1) (w 2) := by
  have hsec := (p5_eq_two_iff_root hw).1 hp
  rcases hsec with ⟨h0, h3, _h4⟩
  have h4 : w 4 = -w 1 - w 2 :=
    root5_four_eq_neg_add_of_zero_zero hw h0 h3
  ext i
  fin_cases i <;> simp [sigmaVec, h0, h3, h4]

abbrev Sigma5 (m : Nat) := {w : ARoot5 m // p5 w.1 = 2}

abbrev SigmaParam (m : Nat) := {ab : ZMod m × ZMod m // ab.1 + ab.2 ≠ 0}

def sigmaPoint {m : Nat} (ab : SigmaParam m) : Sigma5 m :=
  ⟨⟨sigmaVec ab.1.1 ab.1.2, root5_sigmaVec ab.1.1 ab.1.2⟩,
    (p5_sigmaVec_eq_two_iff ab.1.1 ab.1.2).2 ab.2⟩

def sigmaParam {m : Nat} (w : Sigma5 m) : SigmaParam m :=
  ⟨(w.1.1 1, w.1.1 2), by
    have hsec := (p5_eq_two_iff_root w.1.2).1 w.2
    rcases hsec with ⟨h0, h3, h4ne⟩
    intro hsum
    apply h4ne
    have hsum' : w.1.1 1 + w.1.1 2 = 0 := by simpa using hsum
    rw [root5_four_eq_neg_add_of_zero_zero w.1.2 h0 h3]
    rw [show (-w.1.1 1 - w.1.1 2 : ZMod m) = -(w.1.1 1 + w.1.1 2) by abel]
    rw [hsum']
    simp⟩

theorem sigmaParam_left_inverse {m : Nat} :
    Function.LeftInverse (sigmaParam (m := m)) sigmaPoint := by
  intro ab
  apply Subtype.ext
  cases ab with
  | mk ab hab =>
    cases ab with
    | mk a b =>
      simp [sigmaParam, sigmaPoint, sigmaVec]

theorem sigmaParam_right_inverse {m : Nat} :
    Function.RightInverse (sigmaParam (m := m)) sigmaPoint := by
  intro w
  apply Subtype.ext
  apply Subtype.ext
  exact (eq_sigmaVec_of_p5_eq_two w.1.2 w.2).symm

theorem sigmaPoint_bijective {m : Nat} :
    Function.Bijective (sigmaPoint (m := m)) :=
  ⟨Function.LeftInverse.injective sigmaParam_left_inverse,
    Function.RightInverse.surjective sigmaParam_right_inverse⟩

def sigmaBase {m : Nat} (ab : SigmaParam m) : ARoot5 m :=
  (sigmaPoint ab).1

theorem sigmaBase_injective {m : Nat} :
    Function.Injective (sigmaBase (m := m)) := by
  intro s t hst
  apply sigmaPoint_bijective.1
  apply Subtype.ext
  exact hst

theorem not_exists_sigmaBase_of_p5_ne_two {m : Nat} {x : ARoot5 m}
    (hp : p5 x.1 ≠ 2) :
    ¬ exists t : SigmaParam m, x = sigmaBase t := by
  intro h
  rcases h with ⟨t, ht⟩
  apply hp
  rw [ht]
  exact (sigmaPoint t).2

def lastSigmaParam {m : Nat} (a : ZMod m) (ha1 : a ≠ 1) : SigmaParam m :=
  ⟨(a, -1), by
    intro h
    apply ha1
    linear_combination h⟩

theorem zmod_h_add_one_ne_zero {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    (((h + 1 : Nat) : ZMod m)) ≠ 0 := by
  apply zmod_nat_ne_zero (m := m) (k := h + 1) <;> omega

theorem zmod_two_mul_h_add_one {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) :
    (2 : ZMod m) * (((h + 1 : Nat) : ZMod m)) = 1 := by
  have hcast : (((2 * (h + 1) : Nat) : ZMod m)) = 1 := by
    rw [show 2 * (h + 1) = m + 1 by omega]
    simp [Nat.cast_add, ZMod.natCast_self]
  simpa [Nat.cast_mul] using hcast

abbrev NZMod (m : Nat) := {x : ZMod m // x ≠ 0}

def psiNZ {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    NZMod m -> NZMod m :=
  fun s =>
    let c : ZMod m := (h + 1 : Nat)
    if hz : s.1 + c = 0 then
      ⟨c, by
        dsimp [c]
        exact zmod_h_add_one_ne_zero hm hh2⟩
    else
      ⟨s.1 + c, hz⟩

def thetaNZ {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (_hh2 : 2 <= h) (r : Fin (m - 1)) : NZMod m :=
  let c : ZMod m := (h + 1 : Nat)
  ⟨((r.val + 1 : Nat) : ZMod m) * c, by
    dsimp [c]
    intro hzero
    have hcast0 : (((r.val + 1 : Nat) : ZMod m)) = 0 := by
      calc
        (((r.val + 1 : Nat) : ZMod m)) =
            (1 : ZMod m) * (((r.val + 1 : Nat) : ZMod m)) := by ring
        _ = ((2 : ZMod m) * (((h + 1 : Nat) : ZMod m)) : ZMod m) *
            (((r.val + 1 : Nat) : ZMod m)) := by
              rw [zmod_two_mul_h_add_one hm]
        _ = (2 : ZMod m) * ((((r.val + 1 : Nat) : ZMod m)) *
            (((h + 1 : Nat) : ZMod m))) := by ring
        _ = 0 := by rw [hzero]; ring
    have hne : (((r.val + 1 : Nat) : ZMod m)) ≠ 0 := by
      apply zmod_nat_ne_zero (m := m) (k := r.val + 1) <;> omega
    exact hne hcast0⟩

def sigmaArow {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (_hh2 : 2 <= h) (q : Fin (m - 1)) : NZMod m :=
  ⟨(q.val + 1 : Nat), by
    apply zmod_nat_ne_zero (m := m) (k := q.val + 1) <;> omega⟩

theorem zmod_zero_ne_one_of_odd_ge5 {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    (0 : ZMod m) ≠ 1 := by
  have h1 : (1 : ZMod m) ≠ 0 := by
    simpa using zmod_nat_ne_zero (m := m) (k := 1) (by omega) (by omega)
  intro h
  exact h1 h.symm

def lastZeroSigmaParam {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) : SigmaParam m :=
  lastSigmaParam 0 (zmod_zero_ne_one_of_odd_ge5 hm hh2)

def nextSigma {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h)
    (s : SigmaParam m) : SigmaParam m :=
  let a : ZMod m := s.1.1
  let b : ZMod m := s.1.2
  let c : ZMod m := (h + 1 : Nat)
  if hB : b + 1 = 0 then
    if ha : a = 0 then
      ⟨(1, 0), by
        change (1 : ZMod m) + 0 ≠ 0
        simpa using zmod_nat_ne_zero (m := m) (k := 1) (by omega) (by omega)⟩
    else
      ⟨(a, 0), by simpa using ha⟩
  else
    if hz : a + b + c = 0 then
      ⟨(c - (b + 1), b + 1), by
        have hc : c ≠ 0 := by
          dsimp [c]
          exact zmod_h_add_one_ne_zero hm hh2
        intro hsum
        apply hc
        linear_combination hsum⟩
    else
      ⟨(a + b + c - (b + 1), b + 1), by
        intro hsum
        apply hz
        linear_combination hsum⟩

def returnTimeSigma {m h : Nat} [NeZero m]
    (_hm : m = 2 * h + 1) (_hh2 : 2 <= h)
    (s : SigmaParam m) : Nat :=
  let a : ZMod m := s.1.1
  let b : ZMod m := s.1.2
  if b + 1 = 0 then
    if a = 0 then
      m ^ 3 - (m - 1) * (m - 2)
    else
      m - 1
  else
    let r := (a + b).val
    if r < h then
      (h + 1) * m
    else if r = h then
      2 * (h + 1) * m
    else
      (3 * h + 2) * m

def orbitSigma {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h)
    (I : SigmaIdx m) : SigmaParam m :=
  let sNZ := ((psiNZ hm hh2)^[I.2.val]) (sigmaArow hm hh2 I.1)
  let b : ZMod m := (I.2.val : Nat)
  ⟨(sNZ.1 - b, b), by
    intro hzero
    apply sNZ.2
    linear_combination hzero⟩

theorem orbitSigma_sum {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (I : SigmaIdx m) :
    (orbitSigma hm hh2 I).1.1 + (orbitSigma hm hh2 I).1.2 =
      (((psiNZ hm hh2)^[I.2.val]) (sigmaArow hm hh2 I.1)).1 := by
  simp [orbitSigma]

theorem nextSigma_orbitSigma_col_lt {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (I : SigmaIdx m)
    (hcol : I.2.val + 1 < m) :
    nextSigma hm hh2 (orbitSigma hm hh2 I) =
      orbitSigma hm hh2 (I.1, ⟨I.2.val + 1, hcol⟩) := by
  let sNZ := ((psiNZ hm hh2)^[I.2.val]) (sigmaArow hm hh2 I.1)
  have hB : (((I.2.val : Nat) : ZMod m) + 1) ≠ 0 := by
    have hne : (((I.2.val + 1 : Nat) : ZMod m)) ≠ 0 := by
      apply zmod_nat_ne_zero (m := m) (k := I.2.val + 1) <;> omega
    intro hz
    apply hne
    simpa [Nat.cast_add] using hz
  have hiter :
      ((psiNZ hm hh2)^[I.2.val + 1]) (sigmaArow hm hh2 I.1) =
        psiNZ hm hh2 sNZ := by
    dsimp [sNZ]
    exact Function.iterate_succ_apply' (psiNZ hm hh2) I.2.val
      (sigmaArow hm hh2 I.1)
  apply Subtype.ext
  by_cases hz : sNZ.1 + ((h : ZMod m) + 1) = 0
  · have hzLeft :
        (((psiNZ hm hh2)^[I.2.val]) (sigmaArow hm hh2 I.1)).1 +
            ((h : ZMod m) + 1) = 0 := by
      simpa [sNZ] using hz
    simp [orbitSigma, nextSigma, psiNZ, hB, hiter]
    rw [dif_pos hzLeft, dif_pos hz]
    ext <;> ring_nf
  · have hzLeft :
        ¬ (((psiNZ hm hh2)^[I.2.val]) (sigmaArow hm hh2 I.1)).1 +
            ((h : ZMod m) + 1) = 0 := by
      simpa [sNZ] using hz
    simp [orbitSigma, nextSigma, psiNZ, hB, hiter]
    rw [dif_neg hzLeft, dif_neg hz]

theorem returnTimeSigma_last_zero {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    returnTimeSigma hm hh2 (lastZeroSigmaParam hm hh2) =
      m ^ 3 - (m - 1) * (m - 2) := by
  simp [returnTimeSigma, lastZeroSigmaParam, lastSigmaParam]

theorem nextSigma_last_zero {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    nextSigma hm hh2 (lastZeroSigmaParam hm hh2) =
      ⟨(1, 0), by
        change (1 : ZMod m) + 0 ≠ 0
        simpa using zmod_nat_ne_zero (m := m) (k := 1) (by omega) (by omega)⟩ := by
  apply Subtype.ext
  simp [nextSigma, lastZeroSigmaParam, lastSigmaParam]

def blockVec {m : Nat} (x y B z : ZMod m) : Vec5 m :=
  ![x, y, B, 0, z]

theorem root5_blockVec_iff {m : Nat} (x y B z : ZMod m) :
    Root5 m (blockVec x y B z) ↔ x + y + B + z = 0 := by
  unfold Root5 sum5 blockVec
  rw [Fin.sum_univ_five]
  simp [add_assoc]

theorem p5_blockVec_eq_two_iff_root {m : Nat} {x y B z : ZMod m}
    (hw : Root5 m (blockVec x y B z)) :
    p5 (blockVec x y B z) = 2 ↔ x = 0 ∧ z ≠ 0 := by
  rw [p5_eq_two_iff_root hw]
  simp [blockVec]

theorem p5_blockVec_ne_two_of_x_ne_zero {m : Nat} {x y B z : ZMod m}
    (hx : x ≠ 0) :
    p5 (blockVec x y B z) ≠ 2 := by
  rw [p5, zeroMaskMinusOne_eq_mask5]
  by_cases hy : y = 0 <;> by_cases hB : B = 0 <;>
    by_cases hz : z = 0
  all_goals
    simp [blockVec, Lambda1, mask5, row5, hx, hy, hB, hz]

theorem p5_blockVec_eq_four {m : Nat} {x y B z : ZMod m}
    (hx : x ≠ 0) (hB : B ≠ 0) :
    p5 (blockVec x y B z) = 4 := by
  rw [p5]
  rw [zeroMaskMinusOne_eq_mask5]
  by_cases hy : y = 0 <;> by_cases hz : z = 0
  all_goals simp [blockVec, Lambda1, mask5, row5, hx, hB, hy, hz]

theorem p5_blockVec_zero_zero_eq_one {m : Nat} {y B : ZMod m}
    (hy : y ≠ 0) (hB : B ≠ 0) :
    p5 (blockVec 0 y B 0) = 1 := by
  rw [p5]
  rw [zeroMaskMinusOne_eq_mask5]
  simp [blockVec, Lambda1, mask5, row5, hB, hy]

theorem p5_blockVec_zero_zero_eq_one_of_root {m : Nat} {y B : ZMod m}
    (hw : Root5 m (blockVec 0 y B 0)) (hB : B ≠ 0) :
    p5 (blockVec 0 y B 0) = 1 := by
  apply p5_blockVec_zero_zero_eq_one
  · intro hy
    have hroot := (root5_blockVec_iff (m := m) 0 y B 0).1 hw
    rw [hy] at hroot
    exact hB (by simpa using hroot)
  · exact hB

theorem p5_eq_zero_of_two_three_four_ne_zero {m : Nat} {w : Vec5 m}
    (h2 : w 2 ≠ 0) (h3 : w 3 ≠ 0) (h4 : w 4 ≠ 0) :
    p5 w = 0 := by
  rw [p5]
  rw [zeroMaskMinusOne_eq_mask5]
  by_cases h0 : w 0 = 0 <;> by_cases h1 : w 1 = 0
  all_goals simp [Lambda1, mask5, row5, h0, h1, h2, h3, h4]

theorem p5_eq_one_of_two_three_ne_zero_four_zero {m : Nat} {w : Vec5 m}
    (h2 : w 2 ≠ 0) (h3 : w 3 ≠ 0) (h4 : w 4 = 0) :
    p5 w = 1 := by
  rw [p5]
  rw [zeroMaskMinusOne_eq_mask5]
  by_cases h0 : w 0 = 0 <;> by_cases h1 : w 1 = 0
  all_goals simp [Lambda1, mask5, row5, h0, h1, h2, h3, h4]

theorem p5_eq_zero_of_one_three_four_ne_zero {m : Nat} {w : Vec5 m}
    (h1 : w 1 ≠ 0) (h3 : w 3 ≠ 0) (h4 : w 4 ≠ 0) :
    p5 w = 0 := by
  rw [p5]
  rw [zeroMaskMinusOne_eq_mask5]
  by_cases h0 : w 0 = 0 <;> by_cases h2 : w 2 = 0
  all_goals simp [Lambda1, mask5, row5, h0, h1, h2, h3, h4]

theorem p5_eq_three_of_one_three_ne_zero_two_four_zero {m : Nat} {w : Vec5 m}
    (h1 : w 1 ≠ 0) (h3 : w 3 ≠ 0)
    (h2 : w 2 = 0) (h4 : w 4 = 0) :
    p5 w = 3 := by
  rw [p5]
  rw [zeroMaskMinusOne_eq_mask5]
  by_cases h0 : w 0 = 0
  all_goals simp [Lambda1, mask5, row5, h0, h1, h2, h3, h4]

theorem p5_eq_three_of_zero_one_ne_two_three_four_zero {m : Nat} {w : Vec5 m}
    (h0 : w 0 ≠ 0) (h1 : w 1 ≠ 0)
    (h2 : w 2 = 0) (h3 : w 3 = 0) (h4 : w 4 = 0) :
    p5 w = 3 := by
  rw [p5]
  rw [zeroMaskMinusOne_eq_mask5]
  simp [Lambda1, mask5, row5, h0, h1, h2, h3, h4]

theorem p5_eq_four_of_one_two_zero_three_ne_zero_not_zero_zero
    {m : Nat} {w : Vec5 m}
    (h1 : w 1 = 0) (h2 : w 2 = 0) (h3 : w 3 ≠ 0)
    (h04 : w 0 ≠ 0 ∨ w 4 ≠ 0) :
    p5 w = 4 := by
  rw [p5]
  rw [zeroMaskMinusOne_eq_mask5]
  by_cases h0 : w 0 = 0 <;> by_cases h4 : w 4 = 0
  all_goals simp [Lambda1, mask5, row5, h0, h1, h2, h3, h4] at *

theorem p5_EVec_eq_one {m : Nat} {u v : ZMod m}
    (hu : u ≠ 0) (hs : u + v ≠ 0) :
    p5 (EVec u v) = 1 := by
  rw [p5]
  rw [zeroMaskMinusOne_eq_mask5]
  have h4 : (-u - v : ZMod m) ≠ 0 := by
    rw [show (-u - v : ZMod m) = -(u + v) by abel]
    exact neg_ne_zero.mpr hs
  by_cases hv : v = 0
  all_goals simp [EVec, Lambda1, mask5, row5, hu, hv, h4]

def normalizedG0Drift (m : Nat) : Vec5 m :=
  (-3 : ZMod m) • q5 m 0 + q5 m 3

def normalizedGcDrift (m : Nat) (c : Color) : Vec5 m :=
  (-3 : ZMod m) • q5 m c + q5 m (fin5AddNat c 3) + q5 m (fin5AddNat c 4)

theorem ge5_zero_tail_vector (n : Nat) :
    (n + 1 : Nat) • q5 (n + 5) 0 + q5 (n + 5) 4 + q5 (n + 5) 3 =
      normalizedG0Drift (n + 5) + (-q5 (n + 5) 0) := by
  have h : ((n : Nat) : ZMod (n + 5)) + 1 = (-4 : ZMod (n + 5)) := by
    simpa [Nat.cast_add] using zmod_nat_add_one_eq_neg_four n
  ext i
  fin_cases i <;> simp [normalizedG0Drift, q5, e5, nsmul_eq_mul, h]
  all_goals norm_num

set_option maxHeartbeats 2000000 in
-- Finite coordinate check over the five colors/directions; the default heartbeat limit is tight here.
theorem ge5_color_tail_vector (n : Nat) (c p : Color) :
    rotVec c (normalizedG0Drift (n + 5) + q5 (n + 5) p) + (-q5 (n + 5) c) =
      q5 (n + 5) (fin5AddNat p c.val) +
        q5 (n + 5) (fin5AddNat c 3) +
        q5 (n + 5) (fin5AddNat c 4) +
        (n + 1 : Nat) • q5 (n + 5) c := by
  have h : ((n : Nat) : ZMod (n + 5)) + 1 = (-4 : ZMod (n + 5)) := by
    simpa [Nat.cast_add] using zmod_nat_add_one_eq_neg_four n
  ext i
  fin_cases c <;> fin_cases p <;> fin_cases i <;>
    simp [rotVec, normalizedG0Drift, q5, e5, fin5SubNat, fin5AddNat, nsmul_eq_mul, h] <;>
    ring_nf

theorem normalizedG0Drift_eq (m : Nat) :
    normalizedG0Drift m = ![-3, 0, 0, 1, (2 : ZMod m)] := by
  ext i
  fin_cases i <;> simp [normalizedG0Drift, q5, e5]
  norm_num

def normalizedG0Vec {m : Nat} (w : Vec5 m) : Vec5 m :=
  w + normalizedG0Drift m + q5 m (p5 w)

def normalizedG0Delta0 (m : Nat) : Vec5 m := ![-2, 0, 0, 1, (1 : ZMod m)]

def normalizedG0Delta1 (m : Nat) : Vec5 m := ![-3, 1, 0, 1, (1 : ZMod m)]

def normalizedG0Delta2 (m : Nat) : Vec5 m := ![-3, 0, 1, 1, (1 : ZMod m)]

def normalizedG0Delta3 (m : Nat) : Vec5 m := ![-3, 0, 0, 2, (1 : ZMod m)]

def normalizedG0Delta4 (m : Nat) : Vec5 m := ![-3, 0, 0, 1, (2 : ZMod m)]

theorem normalizedG0Vec_eq_of_p5_eq_zero {m : Nat} {w : Vec5 m} (hp : p5 w = 0) :
    normalizedG0Vec w = w + normalizedG0Delta0 m := by
  ext i
  fin_cases i <;> simp [normalizedG0Vec, normalizedG0Drift_eq, normalizedG0Delta0, q5, e5, hp]
  all_goals ring

theorem normalizedG0Vec_eq_of_p5_eq_one {m : Nat} {w : Vec5 m} (hp : p5 w = 1) :
    normalizedG0Vec w = w + normalizedG0Delta1 m := by
  ext i
  fin_cases i <;> simp [normalizedG0Vec, normalizedG0Drift_eq, normalizedG0Delta1, q5, e5, hp]
  all_goals ring

theorem normalizedG0Vec_eq_of_p5_eq_two {m : Nat} {w : Vec5 m} (hp : p5 w = 2) :
    normalizedG0Vec w = w + normalizedG0Delta2 m := by
  ext i
  fin_cases i <;> simp [normalizedG0Vec, normalizedG0Drift_eq, normalizedG0Delta2, q5, e5, hp]
  all_goals ring

theorem normalizedG0Vec_eq_of_p5_eq_three {m : Nat} {w : Vec5 m} (hp : p5 w = 3) :
    normalizedG0Vec w = w + normalizedG0Delta3 m := by
  ext i
  fin_cases i <;> simp [normalizedG0Vec, normalizedG0Drift_eq, normalizedG0Delta3, q5, e5, hp]
  all_goals ring

theorem normalizedG0Vec_eq_of_p5_eq_four {m : Nat} {w : Vec5 m} (hp : p5 w = 4) :
    normalizedG0Vec w = w + normalizedG0Delta4 m := by
  ext i
  fin_cases i <;> simp [normalizedG0Vec, normalizedG0Drift_eq, normalizedG0Delta4, q5, hp]

theorem normalizedG0Vec_blockVec_eq_of_x_ne_zero {m : Nat} {x y B z : ZMod m}
    (hx : x ≠ 0) (hB : B ≠ 0) :
    normalizedG0Vec (blockVec x y B z) = ![x - 3, y, B, 1, z + 2] := by
  rw [normalizedG0Vec_eq_of_p5_eq_four (p5_blockVec_eq_four hx hB)]
  ext i
  fin_cases i <;> simp [blockVec, normalizedG0Delta4]
  all_goals ring

theorem normalizedG0Vec_blockVec_zero_zero_eq_of_y_ne_zero {m : Nat} {y B : ZMod m}
    (hy : y ≠ 0) (hB : B ≠ 0) :
    normalizedG0Vec (blockVec 0 y B 0) = ![-3, y + 1, B, 1, 1] := by
  rw [normalizedG0Vec_eq_of_p5_eq_one (p5_blockVec_zero_zero_eq_one hy hB)]
  ext i
  fin_cases i <;> simp [blockVec, normalizedG0Delta1]

theorem normalizedG0Vec_blockVec_zero_zero_eq_of_root {m : Nat} {y B : ZMod m}
    (hw : Root5 m (blockVec 0 y B 0)) (hB : B ≠ 0) :
    normalizedG0Vec (blockVec 0 y B 0) = ![-3, y + 1, B, 1, 1] := by
  rw [normalizedG0Vec_eq_of_p5_eq_one (p5_blockVec_zero_zero_eq_one_of_root hw hB)]
  ext i
  fin_cases i <;> simp [blockVec, normalizedG0Delta1]

theorem vec5_iterate_eq_add_of_step_eq_add {m : Nat} (f : Vec5 m -> Vec5 m)
    (w delta : Vec5 m) (n : Nat)
    (hstep : forall k : Nat, k < n -> f (f^[k] w) = f^[k] w + delta) :
    f^[n] w = w + n • delta := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hstep_n : f (f^[n] w) = f^[n] w + delta := hstep n (Nat.lt_succ_self n)
      have ih' : f^[n] w = w + n • delta := by
        apply ih
        intro k hk
        exact hstep k (Nat.lt_trans hk (Nat.lt_succ_self n))
      rw [hstep_n, ih']
      ext i
      simp
      ring

theorem normalizedG0Vec_iter_eq_add_delta0_of_p5_eq_zero_until
    {m : Nat} (w : Vec5 m) (n : Nat)
    (hzero : forall k : Nat, k < n -> p5 (((normalizedG0Vec (m := m))^[k]) w) = 0) :
    ((normalizedG0Vec (m := m))^[n]) w = w + n • normalizedG0Delta0 m := by
  apply vec5_iterate_eq_add_of_step_eq_add
  intro k hk
  exact normalizedG0Vec_eq_of_p5_eq_zero (hzero k hk)

theorem zmod_one_add_nat_ne_zero {m s k : Nat} [NeZero m]
    (hk : k < s - 1) (hsm : s < m) :
    ((1 : ZMod m) + (k : ZMod m)) ≠ 0 := by
  have hkpos : 0 < k + 1 := by omega
  have hkm : k + 1 < m := by omega
  have hne : (((k + 1 : Nat) : ZMod m) ≠ 0) :=
    zmod_nat_ne_zero (m := m) (k := k + 1) hkpos hkm
  intro h
  apply hne
  simpa [Nat.cast_add, add_comm] using h

theorem zmod_one_sub_nat_add_nat_ne_zero {m s k : Nat} [NeZero m]
    (hk : k < s - 1) (hsm : s < m) :
    ((1 : ZMod m) - (s : ZMod m) + (k : ZMod m)) ≠ 0 := by
  let r := s - 1 - k
  have hrpos : 0 < r := by omega
  have hrm : r < m := by omega
  have hrne : ((r : Nat) : ZMod m) ≠ 0 := zmod_nat_ne_zero (m := m) (k := r) hrpos hrm
  have hs_eq : s = r + 1 + k := by omega
  have heq : (-(r : ZMod m)) = (1 : ZMod m) - (s : ZMod m) + (k : ZMod m) := by
    rw [hs_eq]
    simp [Nat.cast_add]
    ring
  intro h
  apply hrne
  exact neg_eq_zero.mp (by rw [heq, h])

theorem normalizedG0Vec_iter_eq_add_delta0_of_coords
    {m : Nat} (w : Vec5 m) (n : Nat)
    (h2 : w 2 ≠ 0)
    (h3 : forall k : Nat, k < n -> w 3 + (k : ZMod m) ≠ 0)
    (h4 : forall k : Nat, k < n -> w 4 + (k : ZMod m) ≠ 0) :
    ((normalizedG0Vec (m := m))^[n]) w = w + n • normalizedG0Delta0 m := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have ih' : ((normalizedG0Vec (m := m))^[n]) w = w + n • normalizedG0Delta0 m := by
        apply ih
        · intro k hk
          exact h3 k (Nat.lt_trans hk (Nat.lt_succ_self n))
        · intro k hk
          exact h4 k (Nat.lt_trans hk (Nat.lt_succ_self n))
      rw [ih']
      have hp : p5 (w + n • normalizedG0Delta0 m) = 0 := by
        apply p5_eq_zero_of_two_three_four_ne_zero
        · simpa [normalizedG0Delta0] using h2
        · simpa [normalizedG0Delta0] using h3 n (Nat.lt_succ_self n)
        · simpa [normalizedG0Delta0] using h4 n (Nat.lt_succ_self n)
      rw [normalizedG0Vec_eq_of_p5_eq_zero hp]
      ext i
      fin_cases i <;> simp [normalizedG0Delta0]
      all_goals ring

theorem normalizedG0Vec_iter_eq_add_delta0_of_coords134
    {m : Nat} (w : Vec5 m) (n : Nat)
    (h1 : w 1 ≠ 0)
    (h3 : forall k : Nat, k < n -> w 3 + (k : ZMod m) ≠ 0)
    (h4 : forall k : Nat, k < n -> w 4 + (k : ZMod m) ≠ 0) :
    ((normalizedG0Vec (m := m))^[n]) w = w + n • normalizedG0Delta0 m := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have ih' : ((normalizedG0Vec (m := m))^[n]) w = w + n • normalizedG0Delta0 m := by
        apply ih
        · intro k hk
          exact h3 k (Nat.lt_trans hk (Nat.lt_succ_self n))
        · intro k hk
          exact h4 k (Nat.lt_trans hk (Nat.lt_succ_self n))
      rw [ih']
      have hp : p5 (w + n • normalizedG0Delta0 m) = 0 := by
        apply p5_eq_zero_of_one_three_four_ne_zero
        · simpa [normalizedG0Delta0] using h1
        · simpa [normalizedG0Delta0] using h3 n (Nat.lt_succ_self n)
        · simpa [normalizedG0Delta0] using h4 n (Nat.lt_succ_self n)
      rw [normalizedG0Vec_eq_of_p5_eq_zero hp]
      ext i
      fin_cases i <;> simp [normalizedG0Delta0]
      all_goals ring

theorem normalizedG0Vec_iter_eq_add_delta4_of_coords12_3_04
    {m : Nat} (w : Vec5 m) (n : Nat)
    (h1 : w 1 = 0) (h2 : w 2 = 0)
    (h3 : forall k : Nat, k < n -> w 3 + (k : ZMod m) ≠ 0)
    (h04 : forall k : Nat, k < n ->
      w 0 + (k : ZMod m) * (-3 : ZMod m) ≠ 0 ∨
        w 4 + (k : ZMod m) * (2 : ZMod m) ≠ 0) :
    ((normalizedG0Vec (m := m))^[n]) w = w + n • normalizedG0Delta4 m := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have ih' : ((normalizedG0Vec (m := m))^[n]) w = w + n • normalizedG0Delta4 m := by
        apply ih
        · intro k hk
          exact h3 k (Nat.lt_trans hk (Nat.lt_succ_self n))
        · intro k hk
          exact h04 k (Nat.lt_trans hk (Nat.lt_succ_self n))
      rw [ih']
      have hp : p5 (w + n • normalizedG0Delta4 m) = 4 := by
        apply p5_eq_four_of_one_two_zero_three_ne_zero_not_zero_zero
        · simpa [normalizedG0Delta4] using h1
        · simpa [normalizedG0Delta4] using h2
        · simpa [normalizedG0Delta4] using h3 n (Nat.lt_succ_self n)
        · simpa [normalizedG0Delta4] using h04 n (Nat.lt_succ_self n)
      rw [normalizedG0Vec_eq_of_p5_eq_four hp]
      ext i
      fin_cases i <;> simp [normalizedG0Delta4]
      all_goals ring

theorem normalizedG0Vec_sigmaVec {m : Nat} {a b : ZMod m} (hab : a + b ≠ 0) :
    normalizedG0Vec (sigmaVec a b) = ![-3, a, b + 1, 1, 1 - a - b] := by
  have hp : p5 (sigmaVec a b) = 2 := (p5_sigmaVec_eq_two_iff a b).2 hab
  have hp0 : p5 ![0, a, b, 0, -a - b] = 2 := by simpa [sigmaVec] using hp
  ext i
  fin_cases i <;>
    simp [normalizedG0Vec, normalizedG0Drift_eq, sigmaVec, q5, e5, hp0]
  all_goals ring

theorem zmod_nat_add_one_add_complement {m s : Nat} [NeZero m] (hsm : s < m) :
    ((s : ZMod m) + 1 + ((m - s - 1 : Nat) : ZMod m)) = 0 := by
  have hms_eq : s + 1 + (m - s - 1) = m := by omega
  have hcast : (((s + 1 + (m - s - 1) : Nat) : ZMod m)) = 0 := by
    rw [hms_eq]
    exact ZMod.natCast_self m
  simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hcast

theorem zmod_one_add_complement_eq_neg {m s : Nat} [NeZero m] (hsm : s < m) :
    ((1 : ZMod m) + ((m - s - 1 : Nat) : ZMod m)) = -(s : ZMod m) := by
  have hzero := zmod_nat_add_one_add_complement (m := m) (s := s) hsm
  linear_combination hzero

theorem zmod_nat_add_one_add_nat_ne_zero {m s k : Nat} [NeZero m]
    (hk : k < m - s - 1) (hsm : s < m) :
    ((s : ZMod m) + 1 + (k : ZMod m)) ≠ 0 := by
  have hpos : 0 < s + 1 + k := by omega
  have hlt : s + 1 + k < m := by omega
  have hne := zmod_nat_ne_zero (m := m) (k := s + 1 + k) hpos hlt
  intro h
  apply hne
  simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using h

theorem zmod_nat_add_two_add_nat_ne_zero {m s k : Nat} [NeZero m]
    (hk : k < m - s - 2) :
    ((s : ZMod m) + 2 + (k : ZMod m)) ≠ 0 := by
  have hpos : 0 < s + 2 + k := by omega
  have hlt : s + 2 + k < m := by omega
  have hne := zmod_nat_ne_zero (m := m) (k := s + 2 + k) hpos hlt
  intro h
  apply hne
  simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using h

theorem zmod_nat_add_two_add_complement {m s : Nat} [NeZero m]
    (hs : s < m - 1) :
    ((s : ZMod m) + 2 + ((m - s - 2 : Nat) : ZMod m)) = 0 := by
  have hms_eq : s + 2 + (m - s - 2) = m := by omega
  have hcast : (((s + 2 + (m - s - 2) : Nat) : ZMod m)) = 0 := by
    rw [hms_eq]
    exact ZMod.natCast_self m
  simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hcast

theorem zmod_one_add_nat_ne_zero_of_lt_complement {m s k : Nat} [NeZero m]
    (hk : k < m - s - 1) (hspos : 0 < s) :
    ((1 : ZMod m) + (k : ZMod m)) ≠ 0 := by
  have hpos : 0 < 1 + k := by omega
  have hlt : 1 + k < m := by omega
  have hne := zmod_nat_ne_zero (m := m) (k := 1 + k) hpos hlt
  intro h
  apply hne
  simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using h

theorem iterate_decomp4 {α : Type*} (f : α -> α) (x : α) (n1 n2 : Nat) :
    f^[n2 + (1 + (n1 + 1))] x = f^[n2] (f (f^[n1] (f x))) := by
  rw [Function.iterate_add_apply]
  rw [Function.iterate_add_apply]
  rw [Function.iterate_add_apply]
  rfl

theorem zmod_nat_pred_eq_sub_one {m s : Nat} (hspos : 0 < s) :
    (((s - 1 : Nat) : ZMod m)) = (s : ZMod m) - 1 := by
  have hs_eq : s = s - 1 + 1 := by omega
  rw [hs_eq]
  simp [Nat.cast_add]

theorem zmod_one_sub_add_nat_pred (m s : Nat) (hspos : 0 < s) :
    (1 : ZMod m) - (s : ZMod m) + (((s - 1 : Nat) : ZMod m)) = 0 := by
  rw [zmod_nat_pred_eq_sub_one (m := m) (s := s) hspos]
  ring

theorem zmod_one_add_nat_pred (m s : Nat) (hspos : 0 < s) :
    (1 : ZMod m) + (((s - 1 : Nat) : ZMod m)) = (s : ZMod m) := by
  rw [zmod_nat_pred_eq_sub_one (m := m) (s := s) hspos]
  ring

theorem zmod_first_block_x_pred (m s : Nat) (hspos : 0 < s) :
    (-3 : ZMod m) + -((((s - 1 : Nat) : ZMod m) * 2)) + -3 =
      -3 + -(((s : ZMod m) - 1) * 2) - 3 := by
  rw [zmod_nat_pred_eq_sub_one (m := m) (s := s) hspos]
  ring

theorem normalizedG0Vec_first_block_from_sigma {m : Nat} [NeZero m]
    {a b : ZMod m} {s : Nat}
    (hspos : 0 < s) (hsm : s < m)
    (hs : a + b = (s : ZMod m)) (hB : b + 1 ≠ 0) :
    ((normalizedG0Vec (m := m))^[m]) (sigmaVec a b) =
      ![-2, a + 1, b + 1, 0, -(s : ZMod m)] := by
  let G := normalizedG0Vec (m := m)
  let w0 : Vec5 m := sigmaVec a b
  let w1 : Vec5 m := ![-3, a, b + 1, 1, (1 : ZMod m) - s]
  have hsne : ((s : Nat) : ZMod m) ≠ 0 := zmod_nat_ne_zero (m := m) (k := s) hspos hsm
  have hab : a + b ≠ 0 := by
    intro h
    exact hsne (by simpa [hs] using h)
  have hGw0 : G w0 = w1 := by
    dsimp [G, w0, w1]
    rw [normalizedG0Vec_sigmaVec hab]
    ext i
    fin_cases i <;> simp
    · linear_combination -hs
  let n1 := s - 1
  let n2 := m - s - 1
  have hw1run : G^[n1] w1 = w1 + n1 • normalizedG0Delta0 m := by
    dsimp [G]
    apply normalizedG0Vec_iter_eq_add_delta0_of_coords
    · dsimp [w1]
      simpa using hB
    · intro k hk
      dsimp [w1]
      exact zmod_one_add_nat_ne_zero (m := m) (s := s) (k := k) (by simpa [n1] using hk) hsm
    · intro k hk
      dsimp [w1]
      exact zmod_one_sub_nat_add_nat_ne_zero (m := m) (s := s) (k := k)
        (by simpa [n1] using hk) hsm
  have hp1 : p5 (G^[n1] w1) = 1 := by
    rw [hw1run]
    apply p5_eq_one_of_two_three_ne_zero_four_zero
    · dsimp [w1, n1]
      simp [normalizedG0Delta0]
      simpa [normalizedG0Delta0] using hB
    · dsimp [w1, n1]
      intro h
      apply hsne
      have h' : (1 : ZMod m) + (((s - 1 : Nat) : ZMod m)) = 0 := by
        simpa [normalizedG0Delta0] using h
      simpa [zmod_one_add_nat_pred m s hspos] using h'
    · dsimp [w1, n1]
      simp [normalizedG0Delta0]
      exact zmod_one_sub_add_nat_pred m s hspos
  let w2 : Vec5 m :=
    ![-3 + (s - 1 : ZMod m) * (-2) - 3, a + 1, b + 1, (s : ZMod m) + 1, 1]
  have hAfter1 : G (G^[n1] w1) = w2 := by
    have hp1' : p5 (w1 + n1 • normalizedG0Delta0 m) = 1 := by
      simpa [hw1run] using hp1
    rw [hw1run]
    dsimp [G]
    rw [normalizedG0Vec_eq_of_p5_eq_one hp1']
    dsimp [w1, w2, n1]
    ext i
    fin_cases i <;> simp [normalizedG0Delta0, normalizedG0Delta1]
    · exact zmod_first_block_x_pred m s hspos
    · exact zmod_one_add_nat_pred m s hspos
    · exact zmod_one_sub_add_nat_pred m s hspos
  have hw2run : G^[n2] w2 = w2 + n2 • normalizedG0Delta0 m := by
    dsimp [G]
    apply normalizedG0Vec_iter_eq_add_delta0_of_coords
    · dsimp [w2]
      simpa using hB
    · intro k hk
      dsimp [w2]
      exact zmod_nat_add_one_add_nat_ne_zero (m := m) (s := s) (k := k)
        (by simpa [n2] using hk) hsm
    · intro k hk
      dsimp [w2]
      exact zmod_one_add_nat_ne_zero_of_lt_complement (m := m) (s := s) (k := k)
        (by simpa [n2] using hk) hspos
  have hdecomp : m = n2 + (1 + (n1 + 1)) := by omega
  have hiter : G^[m] w0 = G^[n2] (G (G^[n1] (G w0))) := by
    simpa [hdecomp] using (iterate_decomp4 G w0 n1 n2)
  change G^[m] w0 = ![-2, a + 1, b + 1, 0, -↑s]
  rw [hiter, hGw0, hAfter1, hw2run]
  dsimp [w2, n1, n2]
  ext i
  fin_cases i <;> simp [normalizedG0Delta0]
  · have hzero := zmod_nat_add_one_add_complement (m := m) (s := s) hsm
    have hn2 : ((m - s - 1 : Nat) : ZMod m) = - (s : ZMod m) - 1 := by
      linear_combination hzero
    rw [hn2]
    ring
  · have hzero := zmod_nat_add_one_add_complement (m := m) (s := s) hsm
    simpa [add_assoc, add_comm, add_left_comm] using hzero
  · have hneg := zmod_one_add_complement_eq_neg (m := m) (s := s) hsm
    simpa [add_assoc, add_comm, add_left_comm] using hneg

theorem normalizedG0Vec_first_block_p5_no_earlier {m : Nat} [NeZero m]
    {a b : ZMod m} {s : Nat}
    (hspos : 0 < s) (hsm : s < m)
    (hs : a + b = (s : ZMod m)) (hB : b + 1 ≠ 0) :
    forall k : Nat, 0 < k -> k < m ->
      p5 (((normalizedG0Vec (m := m))^[k]) (sigmaVec a b)) ≠ 2 := by
  intro k hkpos hklt
  let G := normalizedG0Vec (m := m)
  let w0 : Vec5 m := sigmaVec a b
  let w1 : Vec5 m := ![-3, a, b + 1, 1, (1 : ZMod m) - s]
  have hsne : ((s : Nat) : ZMod m) ≠ 0 :=
    zmod_nat_ne_zero (m := m) (k := s) hspos hsm
  have hab : a + b ≠ 0 := by
    intro h
    exact hsne (by simpa [hs] using h)
  have hGw0 : G w0 = w1 := by
    dsimp [G, w0, w1]
    rw [normalizedG0Vec_sigmaVec hab]
    ext i
    fin_cases i <;> simp
    · linear_combination -hs
  by_cases hks : k <= s
  · let j := k - 1
    have hjlt : j < m - 1 := by
      dsimp [j]
      omega
    have hk_eq : k = 1 + j := by
      dsimp [j]
      omega
    have hstate : G^[k] w0 = w1 + j • normalizedG0Delta0 m := by
      have hiter : G^[k] w0 = G^[j] (G w0) := by
        rw [hk_eq]
        have h_eq : 1 + j = j + 1 := by omega
        simpa [h_eq] using (Function.iterate_succ_apply' G j w0)
      rw [hiter, hGw0]
      apply normalizedG0Vec_iter_eq_add_delta0_of_coords
      · dsimp [w1]
        simpa using hB
      · intro r hr
        dsimp [w1]
        exact zmod_one_add_nat_ne_zero (m := m) (s := s) (k := r) (by omega) hsm
      · intro r hr
        dsimp [w1]
        exact zmod_one_sub_nat_add_nat_ne_zero (m := m) (s := s) (k := r)
          (by omega) hsm
    have h3ne : (G^[k] w0) 3 ≠ 0 := by
      rw [hstate]
      dsimp [w1]
      simp [normalizedG0Delta0]
      have hne : (((1 + j : Nat) : ZMod m)) ≠ 0 := by
        apply zmod_nat_ne_zero (m := m) (k := 1 + j) <;> omega
      intro h
      apply hne
      simpa [Nat.cast_add, add_comm] using h
    simpa [G, w0] using p5_ne_two_of_three_ne_zero h3ne
  · let n1 := s - 1
    let j := k - (s + 1)
    let w2 : Vec5 m :=
      ![-3 + (s - 1 : ZMod m) * (-2) - 3, a + 1, b + 1, (s : ZMod m) + 1, 1]
    have hjlt : j < m - s - 1 := by
      dsimp [j]
      omega
    have hk_eq : k = j + (1 + (n1 + 1)) := by
      dsimp [j, n1]
      omega
    have hw1run : G^[n1] w1 = w1 + n1 • normalizedG0Delta0 m := by
      dsimp [G]
      apply normalizedG0Vec_iter_eq_add_delta0_of_coords
      · dsimp [w1]
        simpa using hB
      · intro r hr
        dsimp [w1]
        exact zmod_one_add_nat_ne_zero (m := m) (s := s) (k := r)
          (by simpa [n1] using hr) hsm
      · intro r hr
        dsimp [w1]
        exact zmod_one_sub_nat_add_nat_ne_zero (m := m) (s := s) (k := r)
          (by simpa [n1] using hr) hsm
    have hp1 : p5 (G^[n1] w1) = 1 := by
      rw [hw1run]
      apply p5_eq_one_of_two_three_ne_zero_four_zero
      · dsimp [w1, n1]
        simp [normalizedG0Delta0]
        simpa [normalizedG0Delta0] using hB
      · dsimp [w1, n1]
        intro h
        apply hsne
        have h' : (1 : ZMod m) + (((s - 1 : Nat) : ZMod m)) = 0 := by
          simpa [normalizedG0Delta0] using h
        simpa [zmod_one_add_nat_pred m s hspos] using h'
      · dsimp [w1, n1]
        simp [normalizedG0Delta0]
        exact zmod_one_sub_add_nat_pred m s hspos
    have hAfter1 : G (G^[n1] w1) = w2 := by
      have hp1' : p5 (w1 + n1 • normalizedG0Delta0 m) = 1 := by
        simpa [hw1run] using hp1
      rw [hw1run]
      dsimp [G]
      rw [normalizedG0Vec_eq_of_p5_eq_one hp1']
      dsimp [w1, w2, n1]
      ext i
      fin_cases i <;> simp [normalizedG0Delta0, normalizedG0Delta1]
      · exact zmod_first_block_x_pred m s hspos
      · exact zmod_one_add_nat_pred m s hspos
      · exact zmod_one_sub_add_nat_pred m s hspos
    have hw2run : G^[j] w2 = w2 + j • normalizedG0Delta0 m := by
      dsimp [G]
      apply normalizedG0Vec_iter_eq_add_delta0_of_coords
      · dsimp [w2]
        simpa using hB
      · intro r hr
        dsimp [w2]
        exact zmod_nat_add_one_add_nat_ne_zero (m := m) (s := s) (k := r)
          (by omega) hsm
      · intro r hr
        dsimp [w2]
        exact zmod_one_add_nat_ne_zero_of_lt_complement (m := m) (s := s) (k := r)
          (by omega) hspos
    have hstate : G^[k] w0 = w2 + j • normalizedG0Delta0 m := by
      have hiter : G^[k] w0 = G^[j] (G (G^[n1] (G w0))) := by
        simpa [hk_eq] using (iterate_decomp4 G w0 n1 j)
      rw [hiter, hGw0, hAfter1, hw2run]
    have h3ne : (G^[k] w0) 3 ≠ 0 := by
      rw [hstate]
      dsimp [w2]
      simp [normalizedG0Delta0]
      exact zmod_nat_add_one_add_nat_ne_zero (m := m) (s := s) (k := j) hjlt hsm
    simpa [G, w0] using p5_ne_two_of_three_ne_zero h3ne

theorem zmod_two_sub_nat_add_nat_ne_zero {m s k : Nat} [NeZero m]
    (hk : k < s - 2) (hsm : s < m) :
    ((2 : ZMod m) - (s : ZMod m) + (k : ZMod m)) ≠ 0 := by
  let r := s - 2 - k
  have hrpos : 0 < r := by omega
  have hrm : r < m := by omega
  have hrne : ((r : Nat) : ZMod m) ≠ 0 := zmod_nat_ne_zero (m := m) (k := r) hrpos hrm
  have hs_eq : s = r + 2 + k := by omega
  have heq : (-(r : ZMod m)) = (2 : ZMod m) - (s : ZMod m) + (k : ZMod m) := by
    rw [hs_eq]
    simp [Nat.cast_add]
    ring
  intro h
  apply hrne
  exact neg_eq_zero.mp (by rw [heq, h])

theorem zmod_nat_add_nat_ne_zero_of_lt_complement {m s k : Nat} [NeZero m]
    (hk : k < m - s) (hspos : 0 < s) :
    ((s : ZMod m) + (k : ZMod m)) ≠ 0 := by
  have hpos : 0 < s + k := by omega
  have hlt : s + k < m := by omega
  have hne := zmod_nat_ne_zero (m := m) (k := s + k) hpos hlt
  intro h
  apply hne
  simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using h

theorem zmod_one_add_nat_ne_zero_of_lt_complement_from_two {m s k : Nat} [NeZero m]
    (hk : k < m - s) (hs2 : 2 <= s) :
    ((1 : ZMod m) + (k : ZMod m)) ≠ 0 := by
  have hpos : 0 < 1 + k := by omega
  have hlt : 1 + k < m := by omega
  have hne := zmod_nat_ne_zero (m := m) (k := 1 + k) hpos hlt
  intro h
  apply hne
  simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using h

theorem zmod_nat_add_complement {m s : Nat} [NeZero m] (hsm : s < m) :
    ((s : ZMod m) + ((m - s : Nat) : ZMod m)) = 0 := by
  have hms_eq : s + (m - s) = m := by omega
  have hcast : (((s + (m - s) : Nat) : ZMod m)) = 0 := by
    rw [hms_eq]
    exact ZMod.natCast_self m
  simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hcast

theorem zmod_one_add_complement_eq_one_sub {m s : Nat} [NeZero m] (hsm : s < m) :
    ((1 : ZMod m) + ((m - s : Nat) : ZMod m)) = 1 - (s : ZMod m) := by
  have hzero := zmod_nat_add_complement (m := m) (s := s) hsm
  linear_combination hzero

theorem zmod_nat_sub_two_eq_sub_two {m s : Nat} (hs2 : 2 <= s) :
    (((s - 2 : Nat) : ZMod m)) = (s : ZMod m) - 2 := by
  have hs_eq : s = s - 2 + 2 := by omega
  rw [hs_eq]
  simp [Nat.cast_add]

theorem normalizedG0Vec_block_decrement {m : Nat} [NeZero m]
    {x y B : ZMod m} {s : Nat}
    (hs2 : 2 <= s) (hsm : s < m) (hx : x ≠ 0) (hB : B ≠ 0) :
    ((normalizedG0Vec (m := m))^[m]) (blockVec x y B (-(s : ZMod m))) =
      ![x - 2, y + 1, B, 0, 1 - (s : ZMod m)] := by
  let G := normalizedG0Vec (m := m)
  let w0 : Vec5 m := blockVec x y B (-(s : ZMod m))
  let w1 : Vec5 m := ![x - 3, y, B, 1, (2 : ZMod m) - s]
  have hspos : 0 < s := by omega
  have hGw0 : G w0 = w1 := by
    dsimp [G, w0, w1]
    rw [normalizedG0Vec_blockVec_eq_of_x_ne_zero hx hB]
    ext i
    fin_cases i <;> simp
    all_goals ring
  let n1 := s - 2
  let n2 := m - s
  have hw1run : G^[n1] w1 = w1 + n1 • normalizedG0Delta0 m := by
    dsimp [G]
    apply normalizedG0Vec_iter_eq_add_delta0_of_coords
    · dsimp [w1]
      exact hB
    · intro k hk
      dsimp [w1]
      exact zmod_one_add_nat_ne_zero (m := m) (s := s) (k := k) (by omega) hsm
    · intro k hk
      dsimp [w1]
      exact zmod_two_sub_nat_add_nat_ne_zero (m := m) (s := s) (k := k)
        (by simpa [n1] using hk) hsm
  have hp1 : p5 (G^[n1] w1) = 1 := by
    rw [hw1run]
    apply p5_eq_one_of_two_three_ne_zero_four_zero
    · dsimp [w1, n1]
      simpa [normalizedG0Delta0] using hB
    · dsimp [w1, n1]
      intro h
      have hs1ne : ((s - 1 : Nat) : ZMod m) ≠ 0 := by
        apply zmod_nat_ne_zero (m := m) (k := s - 1) <;> omega
      apply hs1ne
      have h' : (1 : ZMod m) + (((s - 2 : Nat) : ZMod m)) = 0 := by
        simpa [normalizedG0Delta0] using h
      have hpred : (1 : ZMod m) + (((s - 2 : Nat) : ZMod m)) =
          ((s - 1 : Nat) : ZMod m) := by
        have hs2' := zmod_nat_sub_two_eq_sub_two (m := m) (s := s) hs2
        have hs1' := zmod_nat_pred_eq_sub_one (m := m) (s := s) hspos
        rw [hs2', hs1']
        ring
      simpa [hpred] using h'
    · dsimp [w1, n1]
      simp [normalizedG0Delta0]
      rw [zmod_nat_sub_two_eq_sub_two (m := m) (s := s) hs2]
      ring
  let w2 : Vec5 m :=
    ![x - 3 + (s - 2 : ZMod m) * (-2) - 3, y + 1, B, (s : ZMod m), 1]
  have hAfter1 : G (G^[n1] w1) = w2 := by
    have hp1' : p5 (w1 + n1 • normalizedG0Delta0 m) = 1 := by
      simpa [hw1run] using hp1
    rw [hw1run]
    dsimp [G]
    rw [normalizedG0Vec_eq_of_p5_eq_one hp1']
    dsimp [w1, w2, n1]
    ext i
    fin_cases i <;> simp [normalizedG0Delta0, normalizedG0Delta1]
    · rw [zmod_nat_sub_two_eq_sub_two (m := m) (s := s) hs2]
      ring
    · rw [zmod_nat_sub_two_eq_sub_two (m := m) (s := s) hs2]
      ring
    · rw [zmod_nat_sub_two_eq_sub_two (m := m) (s := s) hs2]
      ring
  have hw2run : G^[n2] w2 = w2 + n2 • normalizedG0Delta0 m := by
    dsimp [G]
    apply normalizedG0Vec_iter_eq_add_delta0_of_coords
    · dsimp [w2]
      exact hB
    · intro k hk
      dsimp [w2]
      exact zmod_nat_add_nat_ne_zero_of_lt_complement (m := m) (s := s) (k := k)
        (by simpa [n2] using hk) hspos
    · intro k hk
      dsimp [w2]
      exact zmod_one_add_nat_ne_zero_of_lt_complement_from_two (m := m) (s := s) (k := k)
        (by simpa [n2] using hk) hs2
  have hdecomp : m = n2 + (1 + (n1 + 1)) := by omega
  have hiter : G^[m] w0 = G^[n2] (G (G^[n1] (G w0))) := by
    simpa [hdecomp] using (iterate_decomp4 G w0 n1 n2)
  change G^[m] w0 = ![x - 2, y + 1, B, 0, 1 - ↑s]
  rw [hiter, hGw0, hAfter1, hw2run]
  dsimp [w2, n1, n2]
  ext i
  fin_cases i <;> simp [normalizedG0Delta0]
  · have hzero := zmod_nat_add_complement (m := m) (s := s) hsm
    have hn2 : ((m - s : Nat) : ZMod m) = -(s : ZMod m) := by
      linear_combination hzero
    rw [hn2]
    ring
  · have hzero := zmod_nat_add_complement (m := m) (s := s) hsm
    simpa [add_assoc, add_comm, add_left_comm] using hzero
  · have hcomp := zmod_one_add_complement_eq_one_sub (m := m) (s := s) hsm
    simpa [add_assoc, add_comm, add_left_comm] using hcomp

theorem normalizedG0Vec_block_decrement_p5_no_earlier {m : Nat} [NeZero m]
    {x y B : ZMod m} {s : Nat}
    (hs2 : 2 <= s) (hsm : s < m) (hx : x ≠ 0) (hB : B ≠ 0) :
    forall k : Nat, 0 < k -> k < m ->
      p5 (((normalizedG0Vec (m := m))^[k]) (blockVec x y B (-(s : ZMod m)))) ≠ 2 := by
  intro k hkpos hklt
  let G := normalizedG0Vec (m := m)
  let w0 : Vec5 m := blockVec x y B (-(s : ZMod m))
  let w1 : Vec5 m := ![x - 3, y, B, 1, (2 : ZMod m) - s]
  have hspos : 0 < s := by omega
  have hGw0 : G w0 = w1 := by
    dsimp [G, w0, w1]
    rw [normalizedG0Vec_blockVec_eq_of_x_ne_zero hx hB]
    ext i
    fin_cases i <;> simp
    all_goals ring
  by_cases hks : k <= s - 1
  · let j := k - 1
    have hjlt : j < s - 1 := by
      dsimp [j]
      omega
    have hk_eq : k = 1 + j := by
      dsimp [j]
      omega
    have hstate : G^[k] w0 = w1 + j • normalizedG0Delta0 m := by
      have hiter : G^[k] w0 = G^[j] (G w0) := by
        rw [hk_eq]
        have h_eq : 1 + j = j + 1 := by omega
        simpa [h_eq] using (Function.iterate_succ_apply' G j w0)
      rw [hiter, hGw0]
      apply normalizedG0Vec_iter_eq_add_delta0_of_coords
      · dsimp [w1]
        exact hB
      · intro r hr
        dsimp [w1]
        exact zmod_one_add_nat_ne_zero (m := m) (s := s) (k := r) (by omega) hsm
      · intro r hr
        dsimp [w1]
        exact zmod_two_sub_nat_add_nat_ne_zero (m := m) (s := s) (k := r)
          (by omega) hsm
    have h3ne : (G^[k] w0) 3 ≠ 0 := by
      rw [hstate]
      dsimp [w1]
      simp [normalizedG0Delta0]
      exact zmod_one_add_nat_ne_zero (m := m) (s := s) (k := j) hjlt hsm
    simpa [G, w0] using p5_ne_two_of_three_ne_zero h3ne
  · let n1 := s - 2
    let j := k - s
    let w2 : Vec5 m :=
      ![x - 3 + (s - 2 : ZMod m) * (-2) - 3, y + 1, B, (s : ZMod m), 1]
    have hjlt : j < m - s := by
      dsimp [j]
      omega
    have hk_eq : k = j + (1 + (n1 + 1)) := by
      dsimp [j, n1]
      omega
    have hw1run : G^[n1] w1 = w1 + n1 • normalizedG0Delta0 m := by
      dsimp [G]
      apply normalizedG0Vec_iter_eq_add_delta0_of_coords
      · dsimp [w1]
        exact hB
      · intro r hr
        dsimp [w1]
        exact zmod_one_add_nat_ne_zero (m := m) (s := s) (k := r) (by omega) hsm
      · intro r hr
        dsimp [w1]
        exact zmod_two_sub_nat_add_nat_ne_zero (m := m) (s := s) (k := r)
          (by simpa [n1] using hr) hsm
    have hp1 : p5 (G^[n1] w1) = 1 := by
      rw [hw1run]
      apply p5_eq_one_of_two_three_ne_zero_four_zero
      · dsimp [w1, n1]
        simpa [normalizedG0Delta0] using hB
      · dsimp [w1, n1]
        intro h
        have hs1ne : ((s - 1 : Nat) : ZMod m) ≠ 0 := by
          apply zmod_nat_ne_zero (m := m) (k := s - 1) <;> omega
        apply hs1ne
        have h' : (1 : ZMod m) + (((s - 2 : Nat) : ZMod m)) = 0 := by
          simpa [normalizedG0Delta0] using h
        have hpred : (1 : ZMod m) + (((s - 2 : Nat) : ZMod m)) =
            ((s - 1 : Nat) : ZMod m) := by
          have hs2' := zmod_nat_sub_two_eq_sub_two (m := m) (s := s) hs2
          have hs1' := zmod_nat_pred_eq_sub_one (m := m) (s := s) hspos
          rw [hs2', hs1']
          ring
        simpa [hpred] using h'
      · dsimp [w1, n1]
        simp [normalizedG0Delta0]
        rw [zmod_nat_sub_two_eq_sub_two (m := m) (s := s) hs2]
        ring
    have hAfter1 : G (G^[n1] w1) = w2 := by
      have hp1' : p5 (w1 + n1 • normalizedG0Delta0 m) = 1 := by
        simpa [hw1run] using hp1
      rw [hw1run]
      dsimp [G]
      rw [normalizedG0Vec_eq_of_p5_eq_one hp1']
      dsimp [w1, w2, n1]
      ext i
      fin_cases i <;> simp [normalizedG0Delta0, normalizedG0Delta1]
      · rw [zmod_nat_sub_two_eq_sub_two (m := m) (s := s) hs2]
        ring
      · rw [zmod_nat_sub_two_eq_sub_two (m := m) (s := s) hs2]
        ring
      · rw [zmod_nat_sub_two_eq_sub_two (m := m) (s := s) hs2]
        ring
    have hw2run : G^[j] w2 = w2 + j • normalizedG0Delta0 m := by
      dsimp [G]
      apply normalizedG0Vec_iter_eq_add_delta0_of_coords
      · dsimp [w2]
        exact hB
      · intro r hr
        dsimp [w2]
        exact zmod_nat_add_nat_ne_zero_of_lt_complement (m := m) (s := s) (k := r)
          (by omega) hspos
      · intro r hr
        dsimp [w2]
        exact zmod_one_add_nat_ne_zero_of_lt_complement_from_two (m := m) (s := s) (k := r)
          (by omega) hs2
    have hstate : G^[k] w0 = w2 + j • normalizedG0Delta0 m := by
      have hiter : G^[k] w0 = G^[j] (G (G^[n1] (G w0))) := by
        simpa [hk_eq] using (iterate_decomp4 G w0 n1 j)
      rw [hiter, hGw0, hAfter1, hw2run]
    have h3ne : (G^[k] w0) 3 ≠ 0 := by
      rw [hstate]
      dsimp [w2]
      simp [normalizedG0Delta0]
      exact zmod_nat_add_nat_ne_zero_of_lt_complement (m := m) (s := s) (k := j) hjlt hspos
    simpa [G, w0] using p5_ne_two_of_three_ne_zero h3ne

theorem zmod_one_sub_nat_eq_neg_pred {m n : Nat} (hn : 0 < n) :
    (1 : ZMod m) - (n : ZMod m) = -(((n - 1 : Nat) : ZMod m)) := by
  rw [zmod_nat_pred_eq_sub_one (m := m) (s := n) hn]
  ring

theorem normalizedG0Vec_block_decrement_iter {m : Nat} [NeZero m]
    {x y B : ZMod m} {s r : Nat}
    (hrle : r <= s - 1) (hsm : s < m) (hB : B ≠ 0)
    (hx : forall k : Nat, k < r -> x - (2 : ZMod m) * (k : ZMod m) ≠ 0) :
    (((normalizedG0Vec (m := m))^[m])^[r]) (blockVec x y B (-(s : ZMod m))) =
      blockVec (x - (2 : ZMod m) * (r : ZMod m)) (y + (r : ZMod m)) B
        (-(((s - r : Nat) : ZMod m))) := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      have hrle' : r <= s - 1 := by omega
      have hcur2 : 2 <= s - r := by omega
      have hcurm : s - r < m := by omega
      have hcurpos : 0 < s - r := by omega
      have hxcur : x - (2 : ZMod m) * (r : ZMod m) ≠ 0 := hx r (Nat.lt_succ_self r)
      rw [Function.iterate_succ_apply']
      rw [ih hrle' (by
        intro k hk
        exact hx k (Nat.lt_trans hk (Nat.lt_succ_self r)))]
      have hstep := normalizedG0Vec_block_decrement (m := m) (s := s - r)
        (x := x - (2 : ZMod m) * (r : ZMod m)) (y := y + (r : ZMod m)) (B := B)
        hcur2 hcurm hxcur hB
      rw [hstep]
      ext i
      fin_cases i <;> simp [blockVec]
      · ring
      · ring
      · rw [zmod_one_sub_nat_eq_neg_pred (m := m) (n := s - r) hcurpos]
        have hsr : s - r - 1 = s - Nat.succ r := by omega
        rw [hsr]

theorem normalizedG0Vec_block_decrement_iter_p5_no_earlier {m : Nat} [NeZero m]
    {x y B : ZMod m} {s r : Nat}
    (hrle : r <= s - 1) (hsm : s < m) (hB : B ≠ 0)
    (hx : forall k : Nat, k < r -> x - (2 : ZMod m) * (k : ZMod m) ≠ 0) :
    forall k : Nat, 0 < k -> k < r * m ->
      p5 (((normalizedG0Vec (m := m))^[k]) (blockVec x y B (-(s : ZMod m)))) ≠ 2 := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  induction r generalizing x y s with
  | zero =>
      intro k _ hklt
      simp at hklt
  | succ r ih =>
      intro k hkpos hklt
      have hklt' : k < r * m + m := by
        simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hklt
      have hs2 : 2 <= s := by omega
      have hx0 : x ≠ 0 := by
        simpa using hx 0 (Nat.succ_pos r)
      by_cases hkfirst : k < m
      · exact normalizedG0Vec_block_decrement_p5_no_earlier hs2 hsm hx0 hB k hkpos hkfirst
      · let t := k - m
        have htlt : t < r * m := by
          dsimp [t]
          omega
        by_cases ht0 : t = 0
        · have hk_eq : k = m := by
            dsimp [t] at ht0
            omega
          rw [hk_eq]
          have hstep := normalizedG0Vec_block_decrement (m := m)
            (x := x) (y := y) (B := B) (s := s) hs2 hsm hx0 hB
          rw [hstep]
          by_cases hr0 : r = 0
          · exfalso
            apply hkfirst
            simpa [hk_eq, hr0] using hklt
          · have hxnext : x - 2 ≠ 0 := by
              have hbase := hx 1 (by omega)
              simpa using hbase
            have hblock :
                ![x - 2, y + 1, B, 0, 1 - (s : ZMod m)] =
                  blockVec (x - 2) (y + 1) B (-(((s - 1 : Nat) : ZMod m))) := by
              ext i
              fin_cases i <;> simp [blockVec]
              · rw [zmod_one_sub_nat_eq_neg_pred (m := m) (n := s) (by omega)]
            rw [hblock]
            exact p5_blockVec_ne_two_of_x_ne_zero hxnext
        · have htpos : 0 < t := by omega
          have hk_eq : k = m + t := by
            dsimp [t]
            omega
          rw [hk_eq]
          rw [Nat.add_comm]
          rw [Function.iterate_add_apply]
          have hstep := normalizedG0Vec_block_decrement (m := m)
            (x := x) (y := y) (B := B) (s := s) hs2 hsm hx0 hB
          rw [hstep]
          have hblock :
              ![x - 2, y + 1, B, 0, 1 - (s : ZMod m)] =
                blockVec (x - 2) (y + 1) B (-(((s - 1 : Nat) : ZMod m))) := by
            ext i
            fin_cases i <;> simp [blockVec]
            · rw [zmod_one_sub_nat_eq_neg_pred (m := m) (n := s) (by omega)]
          rw [hblock]
          apply ih
          · omega
          · omega
          · intro j hj
            have hbase := hx (j + 1) (by omega)
            intro hz
            apply hbase
            have heq : x - (2 : ZMod m) * ((j + 1 : Nat) : ZMod m) =
                (x - 2) - (2 : ZMod m) * (j : ZMod m) := by
              simp [Nat.cast_add]
              ring
            rwa [heq]
          · exact htpos
          · exact htlt

theorem zmod_neg_nat_ne_zero {m n : Nat} [NeZero m] (hnpos : 0 < n) (hnm : n < m) :
    (-(n : ZMod m)) ≠ 0 := by
  intro h
  exact zmod_nat_ne_zero (m := m) (k := n) hnpos hnm (neg_eq_zero.mp h)

theorem normalizedG0Vec_sigma_to_neg_one_p5_no_earlier_aux {m : Nat} [NeZero m]
    {a b : ZMod m} {s : Nat}
    (hspos : 0 < s) (hsm : s < m)
    (hs : a + b = (s : ZMod m)) (hB : b + 1 ≠ 0)
    (hneg2 : (-2 : ZMod m) ≠ 0)
    (hx : forall j : Nat, j < s - 1 ->
      (-2 : ZMod m) - (2 : ZMod m) * (j : ZMod m) ≠ 0) :
    forall k : Nat, 0 < k -> k < s * m ->
      p5 (((normalizedG0Vec (m := m))^[k]) (sigmaVec a b)) ≠ 2 := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  intro k hkpos hklt
  let G := normalizedG0Vec (m := m)
  by_cases hkfirst : k < m
  · exact normalizedG0Vec_first_block_p5_no_earlier hspos hsm hs hB k hkpos hkfirst
  · let t := k - m
    have htlt : t < (s - 1) * m := by
      dsimp [t]
      have hsmul : s * m = (s - 1) * m + m := by
        have hs_eq : s = (s - 1) + 1 := by omega
        rw [hs_eq]
        rw [Nat.add_mul]
        simp
      have hklt' : k < (s - 1) * m + m := by
        simpa [hsmul] using hklt
      omega
    have hfirst :
        G^[m] (sigmaVec a b) =
          blockVec (-2) (a + 1) (b + 1) (-(s : ZMod m)) := by
      dsimp [G]
      rw [normalizedG0Vec_first_block_from_sigma hspos hsm hs hB]
      ext i
      fin_cases i <;> simp [blockVec]
    by_cases ht0 : t = 0
    · have hk_eq : k = m := by
        dsimp [t] at ht0
        omega
      rw [hk_eq, hfirst]
      exact p5_blockVec_ne_two_of_x_ne_zero hneg2
    · have htpos : 0 < t := by omega
      have hk_eq : k = m + t := by
        dsimp [t]
        omega
      rw [hk_eq]
      rw [Nat.add_comm]
      rw [Function.iterate_add_apply]
      rw [hfirst]
      exact normalizedG0Vec_block_decrement_iter_p5_no_earlier
        (m := m) (x := (-2 : ZMod m)) (y := a + 1) (B := b + 1)
        (s := s) (r := s - 1) (by omega) hsm hB hx t htpos htlt

theorem zmod_low_first_x_ne {m h s k : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hks : k < s - 1) (hsh : s < h) :
    ((-2 : ZMod m) - (2 : ZMod m) * (k : ZMod m)) ≠ 0 := by
  have hpos : 0 < 2 * (k + 1) := by omega
  have hlt : 2 * (k + 1) < m := by omega
  have hne := zmod_neg_nat_ne_zero (m := m) (n := 2 * (k + 1)) hpos hlt
  intro h
  apply hne
  have heq : (-(↑(2 * (k + 1)) : ZMod m)) =
      (-2 : ZMod m) - (2 : ZMod m) * (k : ZMod m) := by
    simp [Nat.cast_mul, Nat.cast_add]
    ring
  rwa [heq]

theorem normalizedG0Vec_sigma_to_neg_one_low {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) {a b : ZMod m} {s : Nat}
    (hspos : 0 < s) (hsh : s < h)
    (hs : a + b = (s : ZMod m)) (hB : b + 1 ≠ 0) :
    (((normalizedG0Vec (m := m))^[m])^[s]) (sigmaVec a b) =
      blockVec (-(2 : ZMod m) * (s : ZMod m)) (a + (s : ZMod m)) (b + 1) (-1) := by
  let H : Vec5 m -> Vec5 m := (normalizedG0Vec (m := m))^[m]
  let r := s - 1
  have hsm : s < m := by omega
  have hfirst : H (sigmaVec a b) = blockVec (-2) (a + 1) (b + 1) (-(s : ZMod m)) := by
    dsimp [H]
    rw [normalizedG0Vec_first_block_from_sigma hspos hsm hs hB]
    ext i
    fin_cases i <;> simp [blockVec]
  have hdec : H^[r] (blockVec (-2) (a + 1) (b + 1) (-(s : ZMod m))) =
      blockVec ((-2 : ZMod m) - (2 : ZMod m) * (r : ZMod m))
        (a + 1 + (r : ZMod m)) (b + 1) (-(((s - r : Nat) : ZMod m))) := by
    dsimp [H]
    apply normalizedG0Vec_block_decrement_iter
    · dsimp [r]
      omega
    · exact hsm
    · exact hB
    · intro k hk
      dsimp [r] at hk
      exact zmod_low_first_x_ne (m := m) (h := h) (s := s) (k := k) hm hk hsh
  have hiter : H^[s] (sigmaVec a b) = H^[r] (H (sigmaVec a b)) := by
    have hs_eq : s = r + 1 := by dsimp [r]; omega
    simpa [hs_eq] using (Function.iterate_succ_apply' H r (sigmaVec a b))
  rw [hiter, hfirst, hdec]
  dsimp [r]
  ext i
  fin_cases i <;> simp [blockVec]
  · rw [zmod_nat_pred_eq_sub_one (m := m) (s := s) hspos]
    ring
  · rw [zmod_nat_pred_eq_sub_one (m := m) (s := s) hspos]
    ring
  · rw [zmod_nat_pred_eq_sub_one (m := m) (s := s) hspos]
    ring

theorem normalizedG0Vec_sigma_to_neg_one_low_p5_no_earlier {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) {a b : ZMod m} {s : Nat}
    (hspos : 0 < s) (hsh : s < h)
    (hs : a + b = (s : ZMod m)) (hB : b + 1 ≠ 0) :
    forall k : Nat, 0 < k -> k < s * m ->
      p5 (((normalizedG0Vec (m := m))^[k]) (sigmaVec a b)) ≠ 2 := by
  have hneg2 : (-2 : ZMod m) ≠ 0 := by
    simpa using zmod_neg_nat_ne_zero (m := m) (n := 2) (by omega) (by omega)
  apply normalizedG0Vec_sigma_to_neg_one_p5_no_earlier_aux
      (m := m) (a := a) (b := b) (s := s) hspos (by omega) hs hB hneg2
  intro k hk
  exact zmod_low_first_x_ne (m := m) (h := h) (s := s) (k := k) hm hk hsh

theorem zmod_one_add_nat_ne_zero_before_mod {m k : Nat} [NeZero m]
    (hk : k < m - 1) :
    ((1 : ZMod m) + (k : ZMod m)) ≠ 0 := by
  have hpos : 0 < 1 + k := by omega
  have hlt : 1 + k < m := by omega
  have hne := zmod_nat_ne_zero (m := m) (k := 1 + k) hpos hlt
  intro h
  apply hne
  simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using h

theorem zmod_one_add_nat_pred_self {m : Nat} [NeZero m] :
    (1 : ZMod m) + (((m - 1 : Nat) : ZMod m)) = 0 := by
  have hcast : (((m - 1 + 1 : Nat) : ZMod m)) = 0 := by
    rw [show m - 1 + 1 = m by
      have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
      omega]
    exact ZMod.natCast_self m
  simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hcast

theorem zmod_nat_pred_self_eq_neg_one {m : Nat} [NeZero m] :
    (((m - 1 : Nat) : ZMod m)) = (-1 : ZMod m) := by
  have h := zmod_one_add_nat_pred_self (m := m)
  linear_combination h

theorem psiNZ_theta_succ {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (r : Fin (m - 1)) :
    psiNZ hm hh2 (thetaNZ hm hh2 r) = thetaNZ hm hh2 ((finRotate (m - 1)) r) := by
  have hm1pos : 0 < m - 1 := by omega
  haveI : NeZero (m - 1) := ⟨Nat.ne_of_gt hm1pos⟩
  by_cases hlast : r.val + 1 = m - 1
  · rw [finRotate_of_last (n := m - 1) r hlast]
    apply Subtype.ext
    simp [thetaNZ, psiNZ]
    have hzero : ((r.val : ZMod m) + 1) * ((h : ZMod m) + 1) +
        ((h : ZMod m) + 1) = 0 := by
      have hr : ((r.val : ZMod m) + 1) = -1 := by
        have htmp : (((r.val + 1 : Nat) : ZMod m)) = -1 := by
          rw [hlast]
          exact zmod_nat_pred_self_eq_neg_one (m := m)
        simpa [Nat.cast_add] using htmp
      rw [hr]
      ring
    rw [dif_pos hzero]
  · have hlt : r.val + 1 < m - 1 := by omega
    rw [finRotate_of_lt (n := m - 1) r hlt]
    apply Subtype.ext
    simp [thetaNZ, psiNZ]
    have hnonzero : ¬ ((r.val : ZMod m) + 1) * ((h : ZMod m) + 1) +
        ((h : ZMod m) + 1) = 0 := by
      intro hzero
      have hsucc_zero :
          (((r.val + 2 : Nat) : ZMod m) * ((h + 1 : Nat) : ZMod m)) = 0 := by
        calc
          (((r.val + 2 : Nat) : ZMod m) * ((h + 1 : Nat) : ZMod m))
              = (((r.val : ZMod m) + 1) * ((h + 1 : Nat) : ZMod m)) +
                  ((h + 1 : Nat) : ZMod m) := by
                rw [show r.val + 2 = (r.val + 1) + 1 by omega]
                simp [Nat.cast_add]
                ring
          _ = 0 := by
                simpa [Nat.cast_add] using hzero
      have htheta := (thetaNZ hm hh2 (⟨r.val + 1, hlt⟩ : Fin (m - 1))).2
      apply htheta
      simpa [thetaNZ, Nat.cast_add, add_comm, add_left_comm, add_assoc] using hsucc_zero
    rw [dif_neg hnonzero]
    simp
    ring

theorem psiNZ_theta_iter {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (r : Fin (m - 1)) (k : Nat) :
    ((psiNZ hm hh2)^[k]) (thetaNZ hm hh2 r) =
      thetaNZ hm hh2 (((finRotate (m - 1))^[k]) r) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact psiNZ_theta_succ hm hh2 (((finRotate (m - 1))^[k]) r)

theorem psiNZ_theta_period {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (r : Fin (m - 1)) :
    ((psiNZ hm hh2)^[m - 1]) (thetaNZ hm hh2 r) = thetaNZ hm hh2 r := by
  have hm1pos : 0 < m - 1 := by omega
  haveI : NeZero (m - 1) := ⟨Nat.ne_of_gt hm1pos⟩
  rw [psiNZ_theta_iter]
  rw [finRotate_iterate_card]

def thetaPre {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (_hh2 : 2 <= h) (s : NZMod m) : Fin (m - 1) :=
  let y := ((2 : ZMod m) * s.1).val
  ⟨y - 1, by
    have hylt : y < m := ZMod.val_lt ((2 : ZMod m) * s.1)
    have htwo_ne : (2 : ZMod m) * s.1 ≠ 0 := by
      intro hzero
      apply s.2
      have hc := zmod_two_mul_h_add_one hm
      calc
        s.1 = (1 : ZMod m) * s.1 := by ring
        _ = ((2 : ZMod m) * (((h + 1 : Nat) : ZMod m))) * s.1 := by rw [hc]
        _ = (((h + 1 : Nat) : ZMod m)) * ((2 : ZMod m) * s.1) := by ring
        _ = 0 := by rw [hzero]; ring
    have hypos : 0 < y := by
      by_contra hnot
      have hy0 : y = 0 := by omega
      apply htwo_ne
      have hcast := ZMod.natCast_zmod_val ((2 : ZMod m) * s.1)
      simpa [y, hy0] using hcast.symm
    omega⟩

theorem thetaNZ_thetaPre {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (s : NZMod m) :
    thetaNZ hm hh2 (thetaPre hm hh2 s) = s := by
  apply Subtype.ext
  unfold thetaPre thetaNZ
  dsimp
  let y := ((2 : ZMod m) * s.1).val
  have htwo_ne : (2 : ZMod m) * s.1 ≠ 0 := by
    intro hzero
    apply s.2
    have hc := zmod_two_mul_h_add_one hm
    calc
      s.1 = (1 : ZMod m) * s.1 := by ring
      _ = ((2 : ZMod m) * (((h + 1 : Nat) : ZMod m))) * s.1 := by rw [hc]
      _ = (((h + 1 : Nat) : ZMod m)) * ((2 : ZMod m) * s.1) := by ring
      _ = 0 := by rw [hzero]; ring
  have hypos : 0 < y := by
    by_contra hnot
    have hy0 : y = 0 := by omega
    apply htwo_ne
    have hcast := ZMod.natCast_zmod_val ((2 : ZMod m) * s.1)
    simpa [y, hy0] using hcast.symm
  have hsub : y - 1 + 1 = y := Nat.sub_add_cancel (Nat.succ_le_of_lt hypos)
  have hc := zmod_two_mul_h_add_one hm
  calc
    (((y - 1 + 1 : Nat) : ZMod m) * ((h + 1 : Nat) : ZMod m))
        = (((y : Nat) : ZMod m) * ((h + 1 : Nat) : ZMod m)) := by rw [hsub]
    _ = (((2 : ZMod m) * s.1) * ((h + 1 : Nat) : ZMod m)) := by
      rw [ZMod.natCast_zmod_val]
    _ = s.1 := by
      rw [show (2 : ZMod m) * s.1 * (((h + 1 : Nat) : ZMod m)) =
          ((2 : ZMod m) * (((h + 1 : Nat) : ZMod m))) * s.1 by ring]
      rw [hc]
      ring

theorem psiNZ_period {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (s : NZMod m) :
    ((psiNZ hm hh2)^[m - 1]) s = s := by
  rw [← thetaNZ_thetaPre hm hh2 s]
  exact psiNZ_theta_period hm hh2 (thetaPre hm hh2 s)

theorem nextSigma_orbitSigma_last_col_row_lt {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (I : SigmaIdx m)
    (hcol : I.2.val + 1 = m) (hrow : I.1.val + 1 < m - 1) :
    nextSigma hm hh2 (orbitSigma hm hh2 I) =
      orbitSigma hm hh2 (⟨I.1.val + 1, hrow⟩, (⟨0, by omega⟩ : Fin m)) := by
  have hI2 : I.2.val = m - 1 := by omega
  have hperiod :
      ((psiNZ hm hh2)^[I.2.val]) (sigmaArow hm hh2 I.1) =
        sigmaArow hm hh2 I.1 := by
    rw [hI2]
    exact psiNZ_period hm hh2 (sigmaArow hm hh2 I.1)
  have hperiod' :
      ((psiNZ hm hh2)^[I.2.val])
          ⟨((I.1.val : ZMod m) + 1), by
            have hne : (((I.1.val + 1 : Nat) : ZMod m)) ≠ 0 := by
              apply zmod_nat_ne_zero (m := m) (k := I.1.val + 1) <;> omega
            simpa [Nat.cast_add] using hne⟩ =
        ⟨((I.1.val : ZMod m) + 1), by
            have hne : (((I.1.val + 1 : Nat) : ZMod m)) ≠ 0 := by
              apply zmod_nat_ne_zero (m := m) (k := I.1.val + 1) <;> omega
            simpa [Nat.cast_add] using hne⟩ := by
    simpa [sigmaArow, Nat.cast_add] using hperiod
  have hbLast : (((I.2.val : Nat) : ZMod m) + 1) = 0 := by
    rw [hI2]
    simpa [add_comm] using zmod_one_add_nat_pred_self (m := m)
  have haNonzero :
      (((I.1.val + 1 : Nat) : ZMod m) - ((I.2.val : Nat) : ZMod m)) ≠ 0 := by
    intro hz
    have hcast : (((I.1.val + 2 : Nat) : ZMod m)) = 0 := by
      calc
        (((I.1.val + 2 : Nat) : ZMod m))
            = (((I.1.val + 1 : Nat) : ZMod m) - ((I.2.val : Nat) : ZMod m)) := by
              rw [hI2]
              rw [zmod_nat_pred_self_eq_neg_one (m := m)]
              simp [Nat.cast_add]
              ring
        _ = 0 := hz
    have hne : (((I.1.val + 2 : Nat) : ZMod m)) ≠ 0 := by
      apply zmod_nat_ne_zero (m := m) (k := I.1.val + 2) <;> omega
    exact hne hcast
  apply Subtype.ext
  simp [orbitSigma, nextSigma, sigmaArow, hbLast]
  have haNonzero' : (I.1.val : ZMod m) + 1 - ((I.2.val : Nat) : ZMod m) ≠ 0 := by
    simpa [Nat.cast_add] using haNonzero
  simp [hperiod', haNonzero']
  rw [hI2]
  rw [zmod_nat_pred_self_eq_neg_one (m := m)]
  simp

theorem nextSigma_orbitSigma_last_col_last {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (I : SigmaIdx m)
    (hcol : I.2.val + 1 = m) (hrow : I.1.val + 1 = m - 1) :
    nextSigma hm hh2 (orbitSigma hm hh2 I) =
      orbitSigma hm hh2 ((⟨0, by omega⟩ : Fin (m - 1)), (⟨0, by omega⟩ : Fin m)) := by
  have hI2 : I.2.val = m - 1 := by omega
  have hperiod :
      ((psiNZ hm hh2)^[I.2.val]) (sigmaArow hm hh2 I.1) =
        sigmaArow hm hh2 I.1 := by
    rw [hI2]
    exact psiNZ_period hm hh2 (sigmaArow hm hh2 I.1)
  have hperiod' :
      ((psiNZ hm hh2)^[I.2.val])
          ⟨((I.1.val : ZMod m) + 1), by
            have hne : (((I.1.val + 1 : Nat) : ZMod m)) ≠ 0 := by
              apply zmod_nat_ne_zero (m := m) (k := I.1.val + 1) <;> omega
            simpa [Nat.cast_add] using hne⟩ =
        ⟨((I.1.val : ZMod m) + 1), by
            have hne : (((I.1.val + 1 : Nat) : ZMod m)) ≠ 0 := by
              apply zmod_nat_ne_zero (m := m) (k := I.1.val + 1) <;> omega
            simpa [Nat.cast_add] using hne⟩ := by
    simpa [sigmaArow, Nat.cast_add] using hperiod
  have hbLast : (((I.2.val : Nat) : ZMod m) + 1) = 0 := by
    rw [hI2]
    simpa [add_comm] using zmod_one_add_nat_pred_self (m := m)
  have hsLast : (((I.1.val + 1 : Nat) : ZMod m)) = -1 := by
    rw [hrow]
    exact zmod_nat_pred_self_eq_neg_one (m := m)
  have haZero :
      (((I.1.val + 1 : Nat) : ZMod m) - ((I.2.val : Nat) : ZMod m)) = 0 := by
    rw [hI2]
    rw [zmod_nat_pred_self_eq_neg_one (m := m)]
    rw [hsLast]
    ring
  apply Subtype.ext
  simp [orbitSigma, nextSigma, sigmaArow, hbLast]
  have haZero' : (I.1.val : ZMod m) + 1 - ((I.2.val : Nat) : ZMod m) = 0 := by
    simpa [Nat.cast_add] using haZero
  simp [hperiod', haZero']

theorem nextSigma_orbitSigma {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (I : SigmaIdx m) :
    nextSigma hm hh2 (orbitSigma hm hh2 I) =
      orbitSigma hm hh2 (sigmaIdxSucc I) := by
  by_cases hcol : I.2.val + 1 < m
  · rw [sigmaIdxSucc_of_col_lt I hcol]
    exact nextSigma_orbitSigma_col_lt hm hh2 I hcol
  · have hcolEq : I.2.val + 1 = m := by omega
    by_cases hrow : I.1.val + 1 < m - 1
    · rw [sigmaIdxSucc_of_last_col_row_lt I hcolEq hrow]
      exact nextSigma_orbitSigma_last_col_row_lt hm hh2 I hcolEq hrow
    · have hrowEq : I.1.val + 1 = m - 1 := by omega
      rw [sigmaIdxSucc_of_last I hcolEq hrowEq]
      exact nextSigma_orbitSigma_last_col_last hm hh2 I hcolEq hrowEq

def nzToFinPred {m : Nat} [NeZero m] (s : NZMod m) : Fin (m - 1) :=
  ⟨s.1.val - 1, by
    have hpos : 0 < s.1.val := by
      by_contra hnot
      have hzero : s.1.val = 0 := by omega
      exact s.2 ((ZMod.val_eq_zero s.1).mp hzero)
    have hlt := ZMod.val_lt s.1
    omega⟩

theorem sigmaArow_nzToFinPred {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (s : NZMod m) :
    sigmaArow hm hh2 (nzToFinPred s) = s := by
  apply Subtype.ext
  simp [sigmaArow, nzToFinPred]
  have hpos : 0 < s.1.val := by
    by_contra hnot
    have hzero : s.1.val = 0 := by omega
    exact s.2 ((ZMod.val_eq_zero s.1).mp hzero)
  have hsub : s.1.val - 1 + 1 = s.1.val :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
  calc
    (((s.1.val - 1 : Nat) : ZMod m) + 1)
        = (((s.1.val - 1 + 1 : Nat) : ZMod m)) := by
          simp [Nat.cast_add]
    _ = ((s.1.val : Nat) : ZMod m) := by rw [hsub]
    _ = s.1 := ZMod.natCast_zmod_val s.1

theorem nzToFinPred_sigmaArow {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (q : Fin (m - 1)) :
    nzToFinPred (sigmaArow hm hh2 q) = q := by
  apply Fin.ext
  simp [nzToFinPred, sigmaArow]
  have hcast : ((q.val : ZMod m) + 1) = (((q.val + 1 : Nat) : ZMod m)) := by
    simp [Nat.cast_add]
  rw [hcast]
  rw [ZMod.val_natCast_of_lt]
  · omega
  · omega

def orbitSigmaPre {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (s : SigmaParam m) : SigmaIdx m :=
  let b : Fin m := ⟨s.1.2.val, ZMod.val_lt s.1.2⟩
  let sumNZ : NZMod m := ⟨s.1.1 + s.1.2, s.2⟩
  let rowNZ := ((psiNZ hm hh2)^[m - 1 - b.val]) sumNZ
  (nzToFinPred rowNZ, b)

theorem psiNZ_back_forward {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (n : Nat) (hn : n < m) (s : NZMod m) :
    ((psiNZ hm hh2)^[n]) (((psiNZ hm hh2)^[m - 1 - n]) s) = s := by
  rw [← Function.iterate_add_apply]
  have hnle : n <= m - 1 := by omega
  rw [Nat.add_sub_of_le hnle]
  exact psiNZ_period hm hh2 s

theorem orbitSigmaPre_right_inverse {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    Function.RightInverse (orbitSigmaPre hm hh2) (orbitSigma hm hh2) := by
  intro s
  rcases s with ⟨⟨a, b⟩, hab⟩
  apply Subtype.ext
  ext <;> simp [orbitSigmaPre, orbitSigma]
  · have hpsi :
        ((psiNZ hm hh2)^[b.val])
          (sigmaArow hm hh2
            (nzToFinPred (((psiNZ hm hh2)^[m - 1 - b.val]) (⟨a + b, hab⟩ : NZMod m)))) =
          (⟨a + b, hab⟩ : NZMod m) := by
      rw [sigmaArow_nzToFinPred]
      exact psiNZ_back_forward hm hh2 b.val (ZMod.val_lt b) ⟨a + b, hab⟩
    have hpsiVal :
        (((psiNZ hm hh2)^[b.val])
          (sigmaArow hm hh2
            (nzToFinPred (((psiNZ hm hh2)^[m - 1 - b.val]) (⟨a + b, hab⟩ : NZMod m))))).1 =
          a + b := congr_arg Subtype.val hpsi
    rw [hpsiVal]
    ring

theorem psiNZ_forward_back {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (n : Nat) (hn : n < m) (s : NZMod m) :
    ((psiNZ hm hh2)^[m - 1 - n]) (((psiNZ hm hh2)^[n]) s) = s := by
  rw [← Function.iterate_add_apply]
  have hnle : n <= m - 1 := by omega
  have hadd : m - 1 - n + n = m - 1 := Nat.sub_add_cancel hnle
  rw [hadd]
  exact psiNZ_period hm hh2 s

theorem orbitSigmaPre_left_inverse {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    Function.LeftInverse (orbitSigmaPre hm hh2) (orbitSigma hm hh2) := by
  intro I
  apply Prod.ext
  · apply Fin.ext
    simp [orbitSigmaPre, orbitSigma]
    rw [Nat.mod_eq_of_lt I.2.isLt]
    have hrowNZ :
        ((psiNZ hm hh2)^[m - 1 - I.2.val])
          (((psiNZ hm hh2)^[I.2.val]) (sigmaArow hm hh2 I.1)) =
          sigmaArow hm hh2 I.1 := by
      exact psiNZ_forward_back hm hh2 I.2.val I.2.isLt (sigmaArow hm hh2 I.1)
    rw [hrowNZ]
    exact congr_arg Fin.val (nzToFinPred_sigmaArow hm hh2 I.1)
  · apply Fin.ext
    simp [orbitSigmaPre, orbitSigma]
    exact Nat.mod_eq_of_lt I.2.isLt

theorem orbitSigma_bijective {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    Function.Bijective (orbitSigma hm hh2) :=
  ⟨Function.LeftInverse.injective (orbitSigmaPre_left_inverse hm hh2),
    Function.RightInverse.surjective (orbitSigmaPre_right_inverse hm hh2)⟩

theorem nextSigma_single_cycle {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    IsSingleCycleMap (nextSigma hm hh2) := by
  exact single_cycle_of_bijective_semiconj
    (f := sigmaIdxSucc (m := m))
    (g := nextSigma hm hh2)
    (phi := orbitSigma hm hh2)
    (orbitSigma_bijective hm hh2)
    (by
      intro I
      exact (nextSigma_orbitSigma hm hh2 I).symm)
    (sigmaIdxSucc_single_cycle (m := m))

abbrev SigmaBySumCol (m : Nat) := NZMod m × Fin m

noncomputable def finZModEquiv (m : Nat) [NeZero m] : Fin m ≃ ZMod m where
  toFun i := (i.val : ZMod m)
  invFun x := ⟨x.val, ZMod.val_lt x⟩
  left_inv i := by
    apply Fin.ext
    simp
    exact Nat.mod_eq_of_lt i.isLt
  right_inv x := by
    simpa using ZMod.natCast_zmod_val x

noncomputable def sigmaBySumColEquiv {m : Nat} [NeZero m] :
    SigmaParam m ≃ SigmaBySumCol m where
  toFun s := (⟨s.1.1 + s.1.2, s.2⟩, ⟨s.1.2.val, ZMod.val_lt s.1.2⟩)
  invFun rb :=
    let s : ZMod m := rb.1.1
    let b : ZMod m := (rb.2.val : Nat)
    ⟨(s - b, b), by
      intro hzero
      apply rb.1.2
      linear_combination hzero⟩
  left_inv s := by
    rcases s with ⟨⟨a, b⟩, hab⟩
    apply Subtype.ext
    ext
    · simp
    · simpa using ZMod.natCast_zmod_val b
  right_inv rb := by
    rcases rb with ⟨s, b⟩
    apply Prod.ext
    · apply Subtype.ext
      simp
    · apply Fin.ext
      simp
      exact Nat.mod_eq_of_lt b.isLt

def nzReturnTime {m h : Nat} [NeZero m]
    (_hm : m = 2 * h + 1) (_hh2 : 2 <= h) (s : NZMod m) : Nat :=
  let r := s.1.val
  if r < h then
    (h + 1) * m
  else if r = h then
    2 * (h + 1) * m
  else
    (3 * h + 2) * m

theorem returnTimeSigma_by_sum_col_nonlast {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h)
    (r : NZMod m) (j : Fin m) (hj : j.val + 1 < m) :
    returnTimeSigma hm hh2 (sigmaBySumColEquiv.symm (r, j)) =
      nzReturnTime hm hh2 r := by
  have hb : (((j.val : Nat) : ZMod m) + 1) ≠ 0 := by
    intro hz
    have hne : (((j.val + 1 : Nat) : ZMod m)) ≠ 0 := by
      apply zmod_nat_ne_zero (m := m) (k := j.val + 1) <;> omega
    apply hne
    simpa [Nat.cast_add] using hz
  simp [sigmaBySumColEquiv, returnTimeSigma, nzReturnTime, hb]

theorem returnTimeSigma_by_sum_col_last {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h)
    (r : NZMod m) (j : Fin m) (hj : j.val + 1 = m) :
    returnTimeSigma hm hh2 (sigmaBySumColEquiv.symm (r, j)) =
      if r.1 = (-1 : ZMod m) then
        m ^ 3 - (m - 1) * (m - 2)
      else
        m - 1 := by
  have hval : j.val = m - 1 := by omega
  have hb : (((j.val : Nat) : ZMod m) + 1) = 0 := by
    rw [hval]
    simpa [add_comm] using zmod_one_add_nat_pred_self (m := m)
  have ha_zero_iff : r.1 - ((j.val : Nat) : ZMod m) = 0 ↔ r.1 = (-1 : ZMod m) := by
    rw [hval]
    rw [zmod_nat_pred_self_eq_neg_one (m := m)]
    constructor <;> intro h
    · linear_combination h
    · linear_combination h
  simp [sigmaBySumColEquiv, returnTimeSigma, hb, ha_zero_iff]

noncomputable def nzModFinPredEquiv {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) : Fin (m - 1) ≃ NZMod m where
  toFun := sigmaArow hm hh2
  invFun := nzToFinPred
  left_inv := nzToFinPred_sigmaArow hm hh2
  right_inv := sigmaArow_nzToFinPred hm hh2

theorem card_fin_pred_low {m h : Nat} (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    (Finset.univ.filter fun i : Fin (m - 1) => i.val + 1 < h).card = h - 1 := by
  let e : ({i : Fin (m - 1) // i.val + 1 < h} ≃ Fin (h - 1)) := {
    toFun := fun x => ⟨x.1.val, by omega⟩
    invFun := fun y =>
      have hy : y.val < h - 1 := y.isLt
      have hylt : y.val < m - 1 := by omega
      have hprop : (⟨y.val, hylt⟩ : Fin (m - 1)).val + 1 < h := by
        change y.val + 1 < h
        omega
      ⟨⟨y.val, hylt⟩, hprop⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply Fin.ext
      rfl
    right_inv := by
      intro y
      apply Fin.ext
      rfl
  }
  have hcard := Fintype.card_congr e
  rw [Fintype.card_subtype] at hcard
  simpa using hcard

theorem card_fin_pred_mid {m h : Nat} (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    (Finset.univ.filter fun i : Fin (m - 1) => i.val + 1 = h).card = 1 := by
  let e : ({i : Fin (m - 1) // i.val + 1 = h} ≃ Fin 1) := {
    toFun := fun _ => ⟨0, by decide⟩
    invFun := fun _ =>
      have hlt : h - 1 < m - 1 := by omega
      have hprop : (⟨h - 1, hlt⟩ : Fin (m - 1)).val + 1 = h := by
        change h - 1 + 1 = h
        omega
      ⟨⟨h - 1, hlt⟩, hprop⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply Fin.ext
      exact (Nat.eq_sub_of_add_eq x.2).symm
    right_inv := by
      intro y
      apply Fin.ext
      omega
  }
  have hcard := Fintype.card_congr e
  rw [Fintype.card_subtype] at hcard
  simpa using hcard

theorem card_fin_pred_high {m h : Nat} (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    (Finset.univ.filter fun i : Fin (m - 1) => h < i.val + 1).card = h := by
  let e : ({i : Fin (m - 1) // h < i.val + 1} ≃ Fin h) := {
    toFun := fun x => ⟨x.1.val - h, by omega⟩
    invFun := fun y =>
      have hy : y.val < h := y.isLt
      have hlt : h + y.val < m - 1 := by omega
      have hprop : h < (⟨h + y.val, hlt⟩ : Fin (m - 1)).val + 1 := by
        change h < h + y.val + 1
        omega
      ⟨⟨h + y.val, hlt⟩, hprop⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply Fin.ext
      simp
      omega
    right_inv := by
      intro y
      apply Fin.ext
      simp
  }
  have hcard := Fintype.card_congr e
  rw [Fintype.card_subtype] at hcard
  simpa using hcard

theorem sum_ite_const_zero {α : Type} [Fintype α]
    (p : α -> Prop) [DecidablePred p] (A : Nat) :
    (Finset.univ.sum fun x : α => if p x then A else 0) =
      (Finset.univ.filter p).card * A := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_const]
  simp

theorem nzReturnTime_sum_sigmaArow_m3 {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    (Finset.univ.sum fun q : Fin (m - 1) =>
      nzReturnTime hm hh2 (sigmaArow hm hh2 q)) = m ^ 3 := by
  have hval : forall q : Fin (m - 1), (sigmaArow hm hh2 q).1.val = q.val + 1 := by
    intro q
    unfold sigmaArow
    dsimp
    rw [ZMod.val_natCast_of_lt]
    omega
  let A := (h + 1) * m
  let B := 2 * (h + 1) * m
  let C := (3 * h + 2) * m
  have hpoint : forall q : Fin (m - 1),
      nzReturnTime hm hh2 (sigmaArow hm hh2 q) =
        (if q.val + 1 < h then A else 0) +
        (if q.val + 1 = h then B else 0) +
        (if h < q.val + 1 then C else 0) := by
    intro q
    dsimp [nzReturnTime, A, B, C]
    rw [hval q]
    by_cases hlow : q.val + 1 < h
    · have hmid : ¬ q.val + 1 = h := by omega
      have hhigh : ¬ h < q.val + 1 := by omega
      simp [hlow, hmid, hhigh]
    · by_cases hmid : q.val + 1 = h
      · have hhigh : ¬ h < q.val + 1 := by omega
        simp [hlow, hmid, hhigh]
      · have hhigh : h < q.val + 1 := by omega
        simp [hlow, hmid, hhigh]
  calc
    (Finset.univ.sum fun q : Fin (m - 1) => nzReturnTime hm hh2 (sigmaArow hm hh2 q))
        = Finset.univ.sum fun q : Fin (m - 1) =>
            (if q.val + 1 < h then A else 0) +
            (if q.val + 1 = h then B else 0) +
            (if h < q.val + 1 then C else 0) := by
          apply Finset.sum_congr rfl
          intro q _
          exact hpoint q
    _ = (Finset.univ.sum fun q : Fin (m - 1) => if q.val + 1 < h then A else 0) +
        (Finset.univ.sum fun q : Fin (m - 1) => if q.val + 1 = h then B else 0) +
        (Finset.univ.sum fun q : Fin (m - 1) => if h < q.val + 1 then C else 0) := by
          simp [Finset.sum_add_distrib, add_assoc]
    _ = (h - 1) * A + 1 * B + h * C := by
          rw [sum_ite_const_zero, sum_ite_const_zero, sum_ite_const_zero]
          rw [card_fin_pred_low hm hh2, card_fin_pred_mid hm hh2, card_fin_pred_high hm hh2]
    _ = m ^ 3 := by
          dsimp [A, B, C]
          obtain ⟨d, rfl⟩ : ∃ d, h = d + 2 := ⟨h - 2, by omega⟩
          subst m
          simp
          ring

theorem nzReturnTime_sum_m3 {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    (Finset.univ.sum fun r : NZMod m => nzReturnTime hm hh2 r) = m ^ 3 := by
  calc
    (Finset.univ.sum fun r : NZMod m => nzReturnTime hm hh2 r)
        = Finset.univ.sum fun q : Fin (m - 1) =>
            nzReturnTime hm hh2 (sigmaArow hm hh2 q) := by
          exact (Fintype.sum_equiv (nzModFinPredEquiv hm hh2)
            (fun q : Fin (m - 1) => nzReturnTime hm hh2 (sigmaArow hm hh2 q))
            (fun r : NZMod m => nzReturnTime hm hh2 r)
            (by intro q; rfl)).symm
    _ = m ^ 3 := nzReturnTime_sum_sigmaArow_m3 hm hh2

theorem card_fin_last {n : Nat} (hn : 0 < n) :
    (Finset.univ.filter fun i : Fin n => i.val + 1 = n).card = 1 := by
  let e : ({i : Fin n // i.val + 1 = n} ≃ Fin 1) := {
    toFun := fun _ => ⟨0, by decide⟩
    invFun := fun _ =>
      have hlt : n - 1 < n := by omega
      have hprop : (⟨n - 1, hlt⟩ : Fin n).val + 1 = n := by
        change n - 1 + 1 = n
        omega
      ⟨⟨n - 1, hlt⟩, hprop⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply Fin.ext
      exact (Nat.eq_sub_of_add_eq x.2).symm
    right_inv := by
      intro y
      apply Fin.ext
      omega
  }
  have hcard := Fintype.card_congr e
  rw [Fintype.card_subtype] at hcard
  simpa using hcard

theorem card_fin_not_last {n : Nat} (hn : 0 < n) :
    (Finset.univ.filter fun i : Fin n => ¬ i.val + 1 = n).card = n - 1 := by
  have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun i : Fin n => i.val + 1 = n)
  rw [card_fin_last hn] at hsplit
  have huniv : (Finset.univ : Finset (Fin n)).card = n := Fintype.card_fin n
  rw [huniv] at hsplit
  omega

theorem last_time_sub_le (m : Nat) (hm5 : 5 <= m) :
    (m - 1) * (m - 2) <= m ^ 3 := by
  nlinarith [Nat.mul_le_mul (Nat.sub_le m 1) (Nat.sub_le m 2)]

theorem last_column_fin_sum {m : Nat} (hm5 : 5 <= m) :
    (Finset.univ.sum fun q : Fin (m - 1) =>
      if q.val + 1 = m - 1 then
        m ^ 3 - (m - 1) * (m - 2)
      else
        m - 1) = m ^ 3 := by
  let T := m ^ 3 - (m - 1) * (m - 2)
  let B := m - 1
  have hrewrite : forall q : Fin (m - 1),
      (if q.val + 1 = m - 1 then T else B) =
        (if q.val + 1 = m - 1 then T else 0) +
        (if ¬ q.val + 1 = m - 1 then B else 0) := by
    intro q
    by_cases hq : q.val + 1 = m - 1 <;> simp [hq]
  calc
    (Finset.univ.sum fun q : Fin (m - 1) =>
      if q.val + 1 = m - 1 then
        m ^ 3 - (m - 1) * (m - 2)
      else
        m - 1)
        = Finset.univ.sum fun q : Fin (m - 1) =>
            (if q.val + 1 = m - 1 then T else 0) +
            (if ¬ q.val + 1 = m - 1 then B else 0) := by
          apply Finset.sum_congr rfl
          intro q _
          exact hrewrite q
    _ = (Finset.univ.sum fun q : Fin (m - 1) => if q.val + 1 = m - 1 then T else 0) +
        (Finset.univ.sum fun q : Fin (m - 1) => if ¬ q.val + 1 = m - 1 then B else 0) := by
          simp [Finset.sum_add_distrib]
    _ = 1 * T + (m - 2) * B := by
          rw [sum_ite_const_zero, sum_ite_const_zero]
          rw [card_fin_last (n := m - 1) (by omega)]
          rw [card_fin_not_last (n := m - 1) (by omega)]
          rw [show (m - 1) - 1 = m - 2 by omega]
    _ = m ^ 3 := by
          dsimp [T, B]
          rw [one_mul]
          rw [mul_comm (m - 2) (m - 1)]
          exact Nat.sub_add_cancel (last_time_sub_le m hm5)

theorem sigmaArow_eq_neg_one_iff {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (q : Fin (m - 1)) :
    (sigmaArow hm hh2 q).1 = (-1 : ZMod m) ↔ q.val + 1 = m - 1 := by
  constructor
  · intro hq
    have hval : (sigmaArow hm hh2 q).1.val = q.val + 1 := by
      unfold sigmaArow
      dsimp
      rw [ZMod.val_natCast_of_lt]
      omega
    have hnegval : ((-1 : ZMod m).val) = m - 1 := by
      rw [← zmod_nat_pred_self_eq_neg_one (m := m)]
      rw [ZMod.val_natCast_of_lt]
      omega
    have hv := congr_arg ZMod.val hq
    rw [hval, hnegval] at hv
    exact hv
  · intro hq
    unfold sigmaArow
    dsimp
    rw [hq]
    exact zmod_nat_pred_self_eq_neg_one (m := m)

theorem lastColumnReturnTime_sum_m3 {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    (Finset.univ.sum fun r : NZMod m =>
      if r.1 = (-1 : ZMod m) then
        m ^ 3 - (m - 1) * (m - 2)
      else
        m - 1) = m ^ 3 := by
  have hm5 : 5 <= m := by omega
  calc
    (Finset.univ.sum fun r : NZMod m =>
      if r.1 = (-1 : ZMod m) then
        m ^ 3 - (m - 1) * (m - 2)
      else
        m - 1)
        = Finset.univ.sum fun q : Fin (m - 1) =>
            if q.val + 1 = m - 1 then
              m ^ 3 - (m - 1) * (m - 2)
            else
              m - 1 := by
          exact (Fintype.sum_equiv (nzModFinPredEquiv hm hh2)
            (fun q : Fin (m - 1) =>
              if q.val + 1 = m - 1 then
                m ^ 3 - (m - 1) * (m - 2)
              else
                m - 1)
            (fun r : NZMod m =>
              if r.1 = (-1 : ZMod m) then
                m ^ 3 - (m - 1) * (m - 2)
              else
                m - 1)
            (by
              intro q
              dsimp [nzModFinPredEquiv]
              by_cases hq : q.val + 1 = m - 1
              · have hneg : (sigmaArow hm hh2 q).1 = (-1 : ZMod m) :=
                  (sigmaArow_eq_neg_one_iff hm hh2 q).mpr hq
                simp [hq, hneg]
              · have hneg : (sigmaArow hm hh2 q).1 ≠ (-1 : ZMod m) := by
                  intro h
                  exact hq ((sigmaArow_eq_neg_one_iff hm hh2 q).mp h)
                simp [hq, hneg])).symm
    _ = m ^ 3 := last_column_fin_sum hm5

theorem columnReturnTime_sum_m3 {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (j : Fin m) :
    (Finset.univ.sum fun r : NZMod m =>
      returnTimeSigma hm hh2 (sigmaBySumColEquiv.symm (r, j))) = m ^ 3 := by
  by_cases hj : j.val + 1 < m
  · calc
      (Finset.univ.sum fun r : NZMod m =>
        returnTimeSigma hm hh2 (sigmaBySumColEquiv.symm (r, j)))
          = Finset.univ.sum fun r : NZMod m => nzReturnTime hm hh2 r := by
            apply Finset.sum_congr rfl
            intro r _
            exact returnTimeSigma_by_sum_col_nonlast hm hh2 r j hj
      _ = m ^ 3 := nzReturnTime_sum_m3 hm hh2
  · have hjlast : j.val + 1 = m := by omega
    calc
      (Finset.univ.sum fun r : NZMod m =>
        returnTimeSigma hm hh2 (sigmaBySumColEquiv.symm (r, j)))
          = Finset.univ.sum fun r : NZMod m =>
              if r.1 = (-1 : ZMod m) then
                m ^ 3 - (m - 1) * (m - 2)
              else
                m - 1 := by
            apply Finset.sum_congr rfl
            intro r _
            exact returnTimeSigma_by_sum_col_last hm hh2 r j hjlast
      _ = m ^ 3 := lastColumnReturnTime_sum_m3 hm hh2

theorem returnTimeSigma_sum_m4 {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    (Finset.univ.sum fun s : SigmaParam m => returnTimeSigma hm hh2 s) = m ^ 4 := by
  calc
    (Finset.univ.sum fun s : SigmaParam m => returnTimeSigma hm hh2 s)
        = Finset.univ.sum fun rb : SigmaBySumCol m =>
            returnTimeSigma hm hh2 (sigmaBySumColEquiv.symm rb) := by
          exact Fintype.sum_equiv sigmaBySumColEquiv
            (fun s : SigmaParam m => returnTimeSigma hm hh2 s)
            (fun rb : SigmaBySumCol m => returnTimeSigma hm hh2 (sigmaBySumColEquiv.symm rb))
            (by
              intro s
              simpa using (congrArg (fun t : SigmaParam m => returnTimeSigma hm hh2 t)
                (Equiv.symm_apply_apply (sigmaBySumColEquiv (m := m)) s)).symm)
    _ = Finset.univ.sum fun r : NZMod m =>
          Finset.univ.sum fun j : Fin m =>
            returnTimeSigma hm hh2 (sigmaBySumColEquiv.symm (r, j)) := by
          exact Fintype.sum_prod_type _
    _ = Finset.univ.sum fun j : Fin m =>
          Finset.univ.sum fun r : NZMod m =>
            returnTimeSigma hm hh2 (sigmaBySumColEquiv.symm (r, j)) := by
          rw [Finset.sum_comm]
    _ = Finset.univ.sum fun _j : Fin m => m ^ 3 := by
          apply Finset.sum_congr rfl
          intro j _
          exact columnReturnTime_sum_m3 hm hh2 j
    _ = m ^ 4 := by
          simp [Finset.sum_const]
          ring

theorem normalizedG0Vec_block_neg_one {m : Nat} [NeZero m]
    {x y B : ZMod m} (hx : x ≠ 0) (hB : B ≠ 0) :
    ((normalizedG0Vec (m := m))^[m]) (blockVec x y B (-1)) =
      ![x - 1, y, B, 0, (0 : ZMod m)] := by
  let G := normalizedG0Vec (m := m)
  let w0 : Vec5 m := blockVec x y B (-1)
  let w1 : Vec5 m := ![x - 3, y, B, 1, (1 : ZMod m)]
  have hGw0 : G w0 = w1 := by
    dsimp [G, w0, w1]
    rw [normalizedG0Vec_blockVec_eq_of_x_ne_zero hx hB]
    ext i
    fin_cases i <;> simp
    all_goals ring
  let n := m - 1
  have hw1run : G^[n] w1 = w1 + n • normalizedG0Delta0 m := by
    dsimp [G]
    apply normalizedG0Vec_iter_eq_add_delta0_of_coords
    · dsimp [w1]
      exact hB
    · intro k hk
      dsimp [w1]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := k) (by simpa [n] using hk)
    · intro k hk
      dsimp [w1]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := k) (by simpa [n] using hk)
  have hdecomp : m = n + 1 := by
    have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    omega
  have hiter : G^[m] w0 = G^[n] (G w0) := by
    simpa [hdecomp] using (Function.iterate_succ_apply' G n w0)
  change G^[m] w0 = ![x - 1, y, B, 0, 0]
  rw [hiter, hGw0, hw1run]
  dsimp [w1, n]
  ext i
  fin_cases i <;> simp [normalizedG0Delta0]
  · rw [zmod_nat_pred_self_eq_neg_one (m := m)]
    ring
  · exact zmod_one_add_nat_pred_self (m := m)
  · exact zmod_one_add_nat_pred_self (m := m)

theorem normalizedG0Vec_block_neg_one_p5_no_earlier {m : Nat} [NeZero m]
    {x y B : ZMod m} (hx : x ≠ 0) (hB : B ≠ 0) :
    forall k : Nat, 0 < k -> k < m ->
      p5 (((normalizedG0Vec (m := m))^[k]) (blockVec x y B (-1))) ≠ 2 := by
  intro k hkpos hklt
  let G := normalizedG0Vec (m := m)
  let w0 : Vec5 m := blockVec x y B (-1)
  let w1 : Vec5 m := ![x - 3, y, B, 1, (1 : ZMod m)]
  have hGw0 : G w0 = w1 := by
    dsimp [G, w0, w1]
    rw [normalizedG0Vec_blockVec_eq_of_x_ne_zero hx hB]
    ext i
    fin_cases i <;> simp
    all_goals ring
  let j := k - 1
  have hjlt : j < m - 1 := by
    dsimp [j]
    omega
  have hk_eq : k = 1 + j := by
    dsimp [j]
    omega
  have hstate : G^[k] w0 = w1 + j • normalizedG0Delta0 m := by
    have hiter : G^[k] w0 = G^[j] (G w0) := by
      rw [hk_eq]
      have h_eq : 1 + j = j + 1 := by omega
      simpa [h_eq] using (Function.iterate_succ_apply' G j w0)
    rw [hiter, hGw0]
    dsimp [G]
    apply normalizedG0Vec_iter_eq_add_delta0_of_coords
    · dsimp [w1]
      exact hB
    · intro r hr
      dsimp [w1]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := r) (by omega)
    · intro r hr
      dsimp [w1]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := r) (by omega)
  have h3ne : (G^[k] w0) 3 ≠ 0 := by
    rw [hstate]
    dsimp [w1]
    simp [normalizedG0Delta0]
    exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := j) hjlt
  simpa [G, w0] using p5_ne_two_of_three_ne_zero h3ne

theorem zmod_two_add_nat_ne_zero_before_mod {m k : Nat} [NeZero m]
    (hk : k < m - 2) :
    ((2 : ZMod m) + (k : ZMod m)) ≠ 0 := by
  have hpos : 0 < 2 + k := by omega
  have hlt : 2 + k < m := by omega
  have hne := zmod_nat_ne_zero (m := m) (k := 2 + k) hpos hlt
  intro h
  apply hne
  simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using h

theorem zmod_nat_sub_two_self_eq_neg_two {m : Nat} [NeZero m] (hm2 : 2 <= m) :
    (((m - 2 : Nat) : ZMod m)) = (-2 : ZMod m) := by
  have hcast : (((m - 2 + 2 : Nat) : ZMod m)) = 0 := by
    rw [show m - 2 + 2 = m by omega]
    exact ZMod.natCast_self m
  have h : (((m - 2 : Nat) : ZMod m)) + 2 = 0 := by
    simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hcast
  linear_combination h

theorem zmod_two_add_nat_sub_two_self {m : Nat} [NeZero m] (hm2 : 2 <= m) :
    (2 : ZMod m) + (((m - 2 : Nat) : ZMod m)) = 0 := by
  rw [zmod_nat_sub_two_self_eq_neg_two (m := m) hm2]
  ring

theorem normalizedG0Vec_block_zero_of_x_ne_zero {m : Nat} [NeZero m] (hm : 5 <= m)
    {x y B : ZMod m} (hx : x ≠ 0) (hB : B ≠ 0) :
    ((normalizedG0Vec (m := m))^[m]) (blockVec x y B 0) =
      ![x - 2, y + 1, B, 0, (1 : ZMod m)] := by
  let G := normalizedG0Vec (m := m)
  let w0 : Vec5 m := blockVec x y B 0
  let w1 : Vec5 m := ![x - 3, y, B, 1, (2 : ZMod m)]
  have hGw0 : G w0 = w1 := by
    dsimp [G, w0, w1]
    rw [normalizedG0Vec_blockVec_eq_of_x_ne_zero hx hB]
    ext i
    fin_cases i <;> simp
  let n := m - 2
  have hw1run : G^[n] w1 = w1 + n • normalizedG0Delta0 m := by
    dsimp [G]
    apply normalizedG0Vec_iter_eq_add_delta0_of_coords
    · dsimp [w1]
      exact hB
    · intro k hk
      dsimp [w1]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := k) (by omega)
    · intro k hk
      dsimp [w1]
      exact zmod_two_add_nat_ne_zero_before_mod (m := m) (k := k) (by simpa [n] using hk)
  have hp1 : p5 (G^[n] w1) = 1 := by
    rw [hw1run]
    apply p5_eq_one_of_two_three_ne_zero_four_zero
    · dsimp [w1, n]
      simpa [normalizedG0Delta0] using hB
    · dsimp [w1, n]
      intro h
      have hm1ne : ((m - 1 : Nat) : ZMod m) ≠ 0 := by
        apply zmod_nat_ne_zero (m := m) (k := m - 1) <;> omega
      apply hm1ne
      have h' : (1 : ZMod m) + (((m - 2 : Nat) : ZMod m)) = 0 := by
        simpa [normalizedG0Delta0] using h
      have hpred : (1 : ZMod m) + (((m - 2 : Nat) : ZMod m)) =
          ((m - 1 : Nat) : ZMod m) := by
        have hm2' := zmod_nat_sub_two_self_eq_neg_two (m := m) (by omega)
        have hm1' := zmod_nat_pred_self_eq_neg_one (m := m)
        rw [hm2', hm1']
        ring
      simpa [hpred] using h'
    · dsimp [w1, n]
      simp [normalizedG0Delta0]
      exact zmod_two_add_nat_sub_two_self (m := m) (by omega)
  have hdecomp : m = 0 + (1 + (n + 1)) := by omega
  have hiter : G^[m] w0 = G (G^[n] (G w0)) := by
    simpa [hdecomp] using (iterate_decomp4 G w0 n 0)
  change G^[m] w0 = ![x - 2, y + 1, B, 0, 1]
  rw [hiter, hGw0, hw1run]
  have hp1' : p5 (w1 + n • normalizedG0Delta0 m) = 1 := by
    simpa [hw1run] using hp1
  dsimp [G]
  rw [normalizedG0Vec_eq_of_p5_eq_one hp1']
  dsimp [w1, n]
  ext i
  fin_cases i <;> simp [normalizedG0Delta0, normalizedG0Delta1]
  · rw [zmod_nat_sub_two_self_eq_neg_two (m := m) (by omega)]
    ring
  · have htwo := zmod_two_add_nat_sub_two_self (m := m) (by omega)
    linear_combination htwo
  · exact zmod_two_add_nat_sub_two_self (m := m) (by omega)

theorem normalizedG0Vec_block_zero_of_x_ne_zero_p5_no_earlier {m : Nat} [NeZero m]
    (hm : 5 <= m) {x y B : ZMod m} (hx : x ≠ 0) (hB : B ≠ 0) :
    forall k : Nat, 0 < k -> k < m ->
      p5 (((normalizedG0Vec (m := m))^[k]) (blockVec x y B 0)) ≠ 2 := by
  intro k hkpos hklt
  let G := normalizedG0Vec (m := m)
  let w0 : Vec5 m := blockVec x y B 0
  let w1 : Vec5 m := ![x - 3, y, B, 1, (2 : ZMod m)]
  have hGw0 : G w0 = w1 := by
    dsimp [G, w0, w1]
    rw [normalizedG0Vec_blockVec_eq_of_x_ne_zero hx hB]
    ext i
    fin_cases i <;> simp
  let j := k - 1
  have hjlt : j < m - 1 := by
    dsimp [j]
    omega
  have hk_eq : k = 1 + j := by
    dsimp [j]
    omega
  have hstate : G^[k] w0 = w1 + j • normalizedG0Delta0 m := by
    have hiter : G^[k] w0 = G^[j] (G w0) := by
      rw [hk_eq]
      have h_eq : 1 + j = j + 1 := by omega
      simpa [h_eq] using (Function.iterate_succ_apply' G j w0)
    rw [hiter, hGw0]
    dsimp [G]
    apply normalizedG0Vec_iter_eq_add_delta0_of_coords
    · dsimp [w1]
      exact hB
    · intro r hr
      dsimp [w1]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := r) (by omega)
    · intro r hr
      dsimp [w1]
      exact zmod_two_add_nat_ne_zero_before_mod (m := m) (k := r) (by omega)
  have h3ne : (G^[k] w0) 3 ≠ 0 := by
    rw [hstate]
    dsimp [w1]
    simp [normalizedG0Delta0]
    exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := j) hjlt
  simpa [G, w0] using p5_ne_two_of_three_ne_zero h3ne

theorem normalizedG0Vec_block_zero_of_x_zero {m : Nat} [NeZero m]
    {y B : ZMod m} (hy : y ≠ 0) (hB : B ≠ 0) :
    ((normalizedG0Vec (m := m))^[m]) (blockVec 0 y B 0) =
      ![-1, y + 1, B, 0, (0 : ZMod m)] := by
  let G := normalizedG0Vec (m := m)
  let w0 : Vec5 m := blockVec 0 y B 0
  let w1 : Vec5 m := ![-3, y + 1, B, 1, (1 : ZMod m)]
  have hGw0 : G w0 = w1 := by
    dsimp [G, w0, w1]
    rw [normalizedG0Vec_blockVec_zero_zero_eq_of_y_ne_zero hy hB]
  let n := m - 1
  have hw1run : G^[n] w1 = w1 + n • normalizedG0Delta0 m := by
    dsimp [G]
    apply normalizedG0Vec_iter_eq_add_delta0_of_coords
    · dsimp [w1]
      exact hB
    · intro k hk
      dsimp [w1]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := k) (by simpa [n] using hk)
    · intro k hk
      dsimp [w1]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := k) (by simpa [n] using hk)
  have hdecomp : m = n + 1 := by
    have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    omega
  have hiter : G^[m] w0 = G^[n] (G w0) := by
    simpa [hdecomp] using (Function.iterate_succ_apply' G n w0)
  change G^[m] w0 = ![-1, y + 1, B, 0, 0]
  rw [hiter, hGw0, hw1run]
  dsimp [w1, n]
  ext i
  fin_cases i <;> simp [normalizedG0Delta0]
  · rw [zmod_nat_pred_self_eq_neg_one (m := m)]
    ring
  · exact zmod_one_add_nat_pred_self (m := m)
  · exact zmod_one_add_nat_pred_self (m := m)

theorem normalizedG0Vec_block_zero_of_x_zero_p5_no_earlier {m : Nat} [NeZero m]
    {y B : ZMod m} (hy : y ≠ 0) (hB : B ≠ 0) :
    forall k : Nat, 0 < k -> k < m ->
      p5 (((normalizedG0Vec (m := m))^[k]) (blockVec 0 y B 0)) ≠ 2 := by
  intro k hkpos hklt
  let G := normalizedG0Vec (m := m)
  let w0 : Vec5 m := blockVec 0 y B 0
  let w1 : Vec5 m := ![-3, y + 1, B, 1, (1 : ZMod m)]
  have hGw0 : G w0 = w1 := by
    dsimp [G, w0, w1]
    rw [normalizedG0Vec_blockVec_zero_zero_eq_of_y_ne_zero hy hB]
  let j := k - 1
  have hjlt : j < m - 1 := by
    dsimp [j]
    omega
  have hk_eq : k = 1 + j := by
    dsimp [j]
    omega
  have hstate : G^[k] w0 = w1 + j • normalizedG0Delta0 m := by
    have hiter : G^[k] w0 = G^[j] (G w0) := by
      rw [hk_eq]
      have h_eq : 1 + j = j + 1 := by omega
      simpa [h_eq] using (Function.iterate_succ_apply' G j w0)
    rw [hiter, hGw0]
    dsimp [G]
    apply normalizedG0Vec_iter_eq_add_delta0_of_coords
    · dsimp [w1]
      exact hB
    · intro r hr
      dsimp [w1]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := r) (by omega)
    · intro r hr
      dsimp [w1]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := r) (by omega)
  have h3ne : (G^[k] w0) 3 ≠ 0 := by
    rw [hstate]
    dsimp [w1]
    simp [normalizedG0Delta0]
    exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := j) hjlt
  simpa [G, w0] using p5_ne_two_of_three_ne_zero h3ne

theorem zmod_neg_nat_pred_self_eq_one {m : Nat} [NeZero m] :
    (-(((m - 1 : Nat) : ZMod m))) = 1 := by
  rw [zmod_nat_pred_self_eq_neg_one (m := m)]
  ring

theorem zmod_nat_sub_sub_one_eq {m h s : Nat} (hsh : s < h) :
    (((h - s - 1 : Nat) : ZMod m)) = (h : ZMod m) - (s : ZMod m) - 1 := by
  have heq : h - s - 1 + (s + 1) = h := by omega
  have hcast : (((h - s - 1 + (s + 1) : Nat) : ZMod m)) = (h : ZMod m) := by
    rw [heq]
  have hcast' : (((h - s - 1 : Nat) : ZMod m)) + ((s : ZMod m) + 1) =
      (h : ZMod m) := by
    simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hcast
  linear_combination hcast'

theorem zmod_low_zero_x_ne {m h s : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hspos : 0 < s) (hsh : s < h) :
    ((-2 : ZMod m) * (s : ZMod m) - 1) ≠ 0 := by
  have hpos : 0 < 2 * s + 1 := by omega
  have hlt : 2 * s + 1 < m := by omega
  have hne := zmod_neg_nat_ne_zero (m := m) (n := 2 * s + 1) hpos hlt
  intro h
  apply hne
  have heq : (-(↑(2 * s + 1) : ZMod m)) = (-2 : ZMod m) * (s : ZMod m) - 1 := by
    simp [Nat.cast_mul, Nat.cast_add]
    ring
  rwa [heq]

theorem zmod_low_second_x_ne {m h s k : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hspos : 0 < s) (hsh : s < h) (hk : k < h - s - 1) :
    ((-2 : ZMod m) * (s : ZMod m) - 3 - (2 : ZMod m) * (k : ZMod m)) ≠ 0 := by
  have hpos : 0 < 2 * s + 3 + 2 * k := by omega
  have hlt : 2 * s + 3 + 2 * k < m := by omega
  have hne := zmod_neg_nat_ne_zero (m := m) (n := 2 * s + 3 + 2 * k) hpos hlt
  intro h
  apply hne
  have heq : (-(↑(2 * s + 3 + 2 * k) : ZMod m)) =
      (-2 : ZMod m) * (s : ZMod m) - 3 - (2 : ZMod m) * (k : ZMod m) := by
    simp [Nat.cast_mul, Nat.cast_add]
    ring
  rwa [heq]

theorem normalizedG0Vec_low_neg_one_step {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) {a b : ZMod m} {s : Nat}
    (hspos : 0 < s) (hsh : s < h) (hB : b + 1 ≠ 0) :
    ((normalizedG0Vec (m := m))^[m])
      (blockVec (-(2 : ZMod m) * (s : ZMod m)) (a + (s : ZMod m)) (b + 1) (-1)) =
      blockVec ((-2 : ZMod m) * (s : ZMod m) - 1) (a + (s : ZMod m))
        (b + 1) 0 := by
  have hx : (-(2 : ZMod m) * (s : ZMod m)) ≠ 0 := by
    have hpos : 0 < 2 * s := by omega
    have hlt : 2 * s < m := by omega
    have hne := zmod_neg_nat_ne_zero (m := m) (n := 2 * s) hpos hlt
    intro h
    exact hne (by simpa [Nat.cast_mul] using h)
  rw [normalizedG0Vec_block_neg_one hx hB]
  ext i
  fin_cases i <;> simp [blockVec]

theorem normalizedG0Vec_low_zero_step {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) {a b : ZMod m} {s : Nat}
    (hspos : 0 < s) (hsh : s < h) (hB : b + 1 ≠ 0) :
    ((normalizedG0Vec (m := m))^[m])
      (blockVec ((-2 : ZMod m) * (s : ZMod m) - 1) (a + (s : ZMod m)) (b + 1) 0) =
      blockVec ((-2 : ZMod m) * (s : ZMod m) - 3) (a + (s : ZMod m) + 1)
        (b + 1) (-(((m - 1 : Nat) : ZMod m))) := by
  have hx := zmod_low_zero_x_ne (m := m) (h := h) (s := s) hm hspos hsh
  rw [normalizedG0Vec_block_zero_of_x_ne_zero (hm := by omega) hx hB]
  ext i
  fin_cases i <;> simp [blockVec, zmod_neg_nat_pred_self_eq_one]
  all_goals ring

theorem normalizedG0Vec_low_tail_p5_no_earlier {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) {a b : ZMod m} {s : Nat}
    (hspos : 0 < s) (hsh : s < h) (hB : b + 1 ≠ 0) :
    forall k : Nat, 0 < k -> k < (h + 1 - s) * m ->
      p5 (((normalizedG0Vec (m := m))^[k])
        (blockVec (-(2 : ZMod m) * (s : ZMod m)) (a + (s : ZMod m))
          (b + 1) (-1))) ≠ 2 := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hm5 : 5 <= m := by omega
  let G := normalizedG0Vec (m := m)
  let x0 : ZMod m := -(2 : ZMod m) * (s : ZMod m)
  let y0 : ZMod m := a + (s : ZMod m)
  let B : ZMod m := b + 1
  have hx0 : x0 ≠ 0 := by
    dsimp [x0]
    have hpos : 0 < 2 * s := by omega
    have hlt : 2 * s < m := by omega
    have hne := zmod_neg_nat_ne_zero (m := m) (n := 2 * s) hpos hlt
    intro h
    exact hne (by simpa [Nat.cast_mul] using h)
  have hx1 : (-2 : ZMod m) * (s : ZMod m) - 1 ≠ 0 :=
    zmod_low_zero_x_ne (m := m) (h := h) (s := s) hm hspos hsh
  have hx1n : -((2 : ZMod m) * (s : ZMod m)) - 1 ≠ 0 := by
    intro hzero
    apply hx1
    have heq : (-2 : ZMod m) * (s : ZMod m) - 1 =
        -((2 : ZMod m) * (s : ZMod m)) - 1 := by ring
    rwa [heq]
  intro k hkpos hklt
  by_cases hkfirst : k < m
  · dsimp [G, x0, y0, B]
    exact normalizedG0Vec_block_neg_one_p5_no_earlier hx0 hB k hkpos hkfirst
  · let u := k - m
    have htail1 : u < (h - s) * m := by
      dsimp [u]
      have hsplit : (h + 1 - s) * m = (h - s) * m + m := by
        have hlen : h + 1 - s = (h - s) + 1 := by omega
        rw [hlen]
        rw [Nat.add_mul]
        simp
      have hklt' : k < (h - s) * m + m := by
        simpa [hsplit] using hklt
      omega
    have hk_eq : k = m + u := by
      dsimp [u]
      omega
    rw [hk_eq]
    rw [Nat.add_comm]
    rw [Function.iterate_add_apply]
    dsimp [G, x0, y0, B]
    rw [normalizedG0Vec_low_neg_one_step (m := m) (h := h) hm
      (a := a) (b := b) (s := s) hspos hsh hB]
    by_cases hu0 : u = 0
    · simp [hu0]
      exact p5_blockVec_ne_two_of_x_ne_zero hx1n
    · have hupos : 0 < u := by omega
      by_cases hufirst : u < m
      · exact normalizedG0Vec_block_zero_of_x_ne_zero_p5_no_earlier
          (m := m) hm5 hx1 hB u hupos hufirst
      · let v := u - m
        have hvlt : v < (h - s - 1) * m := by
          dsimp [v]
          have hsplit : (h - s) * m = (h - s - 1) * m + m := by
            have hlen : h - s = (h - s - 1) + 1 := by omega
            rw [hlen]
            rw [Nat.add_mul]
            simp
          have hult' : u < (h - s - 1) * m + m := by
            simpa [hsplit] using htail1
          omega
        by_cases hv0 : v = 0
        · have hu_eq : u = m := by
            dsimp [v] at hv0
            omega
          rw [hu_eq]
          rw [normalizedG0Vec_low_zero_step (m := m) (h := h) hm
            (a := a) (b := b) (s := s) hspos hsh hB]
          have hr2pos : 0 < h - s - 1 := by
            by_contra hnot
            have hr20 : h - s - 1 = 0 := by omega
            have hlen2 : h + 1 - s = 2 := by omega
            have hk_eq2 : k = 2 * m := by
              rw [hk_eq, hu_eq]
              omega
            have hklt2 : k < 2 * m := by
              simpa [hlen2] using hklt
            omega
          have hx2 : (-2 : ZMod m) * (s : ZMod m) - 3 ≠ 0 := by
            simpa using zmod_low_second_x_ne (m := m) (h := h) (s := s) (k := 0)
              hm hspos hsh hr2pos
          exact p5_blockVec_ne_two_of_x_ne_zero hx2
        · have hvpos : 0 < v := by omega
          have hu_eq : u = m + v := by
            dsimp [v]
            omega
          rw [hu_eq]
          rw [Nat.add_comm]
          rw [Function.iterate_add_apply]
          rw [normalizedG0Vec_low_zero_step (m := m) (h := h) hm
            (a := a) (b := b) (s := s) hspos hsh hB]
          apply normalizedG0Vec_block_decrement_iter_p5_no_earlier
              (m := m) (x := (-2 : ZMod m) * (s : ZMod m) - 3)
              (y := a + (s : ZMod m) + 1) (B := b + 1)
              (s := m - 1) (r := h - s - 1)
          · omega
          · omega
          · exact hB
          · intro j hj
            exact zmod_low_second_x_ne (m := m) (h := h) (s := s) (k := j)
              hm hspos hsh hj
          · exact hvpos
          · exact hvlt

theorem normalizedG0Vec_first_return_low {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) {a b : ZMod m} {s : Nat}
    (hspos : 0 < s) (hsh : s < h)
    (hs : a + b = (s : ZMod m)) (hB : b + 1 ≠ 0) :
    (((normalizedG0Vec (m := m))^[m])^[h + 1]) (sigmaVec a b) =
      sigmaVec (a + (h : ZMod m)) (b + 1) := by
  let H : Vec5 m -> Vec5 m := (normalizedG0Vec (m := m))^[m]
  let r2 := h - s - 1
  have hsigma_neg := normalizedG0Vec_sigma_to_neg_one_low (m := m) (h := h)
    hm hspos hsh hs hB
  have hsplit : h + 1 = (h + 1 - s) + s := by omega
  have hiter1 : H^[h + 1] (sigmaVec a b) = H^[h + 1 - s] (H^[s] (sigmaVec a b)) := by
    conv_lhs => rw [hsplit]
    rw [Function.iterate_add_apply]
  have hrem_eq : h + 1 - s = r2 + (1 + (0 + 1)) := by dsimp [r2]; omega
  have hiter2 : H^[h + 1 - s]
      (blockVec (-(2 : ZMod m) * (s : ZMod m)) (a + (s : ZMod m)) (b + 1) (-1)) =
      H^[r2] (H (H (blockVec (-(2 : ZMod m) * (s : ZMod m))
        (a + (s : ZMod m)) (b + 1) (-1)))) := by
    calc
      H^[h + 1 - s]
          (blockVec (-(2 : ZMod m) * (s : ZMod m)) (a + (s : ZMod m)) (b + 1) (-1)) =
        H^[r2 + (1 + (0 + 1))]
          (blockVec (-(2 : ZMod m) * (s : ZMod m)) (a + (s : ZMod m)) (b + 1) (-1)) := by
          rw [hrem_eq]
      _ = H^[r2] (H (H (blockVec (-(2 : ZMod m) * (s : ZMod m))
        (a + (s : ZMod m)) (b + 1) (-1)))) := by
        simpa using (iterate_decomp4 H
          (blockVec (-(2 : ZMod m) * (s : ZMod m)) (a + (s : ZMod m)) (b + 1) (-1))
          0 r2)
  rw [hiter1, hsigma_neg, hiter2]
  change ((normalizedG0Vec (m := m))^[m])^[r2]
      (((normalizedG0Vec (m := m))^[m])
        (((normalizedG0Vec (m := m))^[m])
          (blockVec (-(2 : ZMod m) * (s : ZMod m)) (a + (s : ZMod m)) (b + 1) (-1)))) =
    sigmaVec (a + (h : ZMod m)) (b + 1)
  rw [normalizedG0Vec_low_neg_one_step (m := m) (h := h) hm (a := a) (b := b)
    (s := s) hspos hsh hB]
  rw [normalizedG0Vec_low_zero_step (m := m) (h := h) hm (a := a) (b := b)
    (s := s) hspos hsh hB]
  have hdec2 : ((normalizedG0Vec (m := m))^[m])^[r2]
      (blockVec ((-2 : ZMod m) * (s : ZMod m) - 3)
        (a + (s : ZMod m) + 1) (b + 1) (-(((m - 1 : Nat) : ZMod m)))) =
      blockVec (((-2 : ZMod m) * (s : ZMod m) - 3) - (2 : ZMod m) * (r2 : ZMod m))
        (a + (s : ZMod m) + 1 + (r2 : ZMod m)) (b + 1)
        (-(((m - 1 - r2 : Nat) : ZMod m))) := by
    apply normalizedG0Vec_block_decrement_iter
    · dsimp [r2]
      omega
    · omega
    · exact hB
    · intro k hk
      dsimp [r2] at hk
      exact zmod_low_second_x_ne (m := m) (h := h) (s := s) (k := k) hm hspos hsh hk
  rw [hdec2]
  ext i
  fin_cases i <;> simp [blockVec, sigmaVec]
  · have hmzero : ((2 * h + 1 : Nat) : ZMod m) = 0 := by
      rw [← hm]
      exact ZMod.natCast_self m
    have hmzero' : (2 : ZMod m) * (h : ZMod m) + 1 = 0 := by
      simpa [Nat.cast_mul, Nat.cast_add] using hmzero
    rw [zmod_nat_sub_sub_one_eq (m := m) hsh]
    linear_combination -hmzero'
  · rw [zmod_nat_sub_sub_one_eq (m := m) hsh]
    ring
  · have hmsub : m - 1 - r2 = h + s + 1 := by dsimp [r2]; omega
    rw [hmsub]
    simp [Nat.cast_add]
    rw [← hs]
    ring

theorem normalizedG0Vec_first_return_low_p5_no_earlier {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) {a b : ZMod m} {s : Nat}
    (hspos : 0 < s) (hsh : s < h)
    (hs : a + b = (s : ZMod m)) (hB : b + 1 ≠ 0) :
    forall k : Nat, 0 < k -> k < (h + 1) * m ->
      p5 (((normalizedG0Vec (m := m))^[k]) (sigmaVec a b)) ≠ 2 := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  intro k hkpos hklt
  let G := normalizedG0Vec (m := m)
  change p5 (G^[k] (sigmaVec a b)) ≠ 2
  by_cases hkprefix : k < s * m
  · simpa [G] using normalizedG0Vec_sigma_to_neg_one_low_p5_no_earlier
      (m := m) (h := h) hm (a := a) (b := b) (s := s) hspos hsh hs hB
      k hkpos hkprefix
  · let t := k - s * m
    have httail : t < (h + 1 - s) * m := by
      dsimp [t]
      have hsplit : (h + 1) * m = s * m + (h + 1 - s) * m := by
        have hlen : h + 1 = s + (h + 1 - s) := by omega
        rw [hlen]
        rw [Nat.add_mul]
        simp
      have hklt' : k < s * m + (h + 1 - s) * m := by
        simpa [hsplit] using hklt
      omega
    have hprefix_state :
        G^[s * m] (sigmaVec a b) =
          blockVec (-(2 : ZMod m) * (s : ZMod m)) (a + (s : ZMod m))
            (b + 1) (-1) := by
      dsimp [G]
      rw [Nat.mul_comm s m]
      rw [Function.iterate_mul]
      exact normalizedG0Vec_sigma_to_neg_one_low (m := m) (h := h)
        hm (a := a) (b := b) (s := s) hspos hsh hs hB
    by_cases ht0 : t = 0
    · have hk_eq : k = s * m := by
        dsimp [t] at ht0
        omega
      rw [hk_eq, hprefix_state]
      have hx0 : (-(2 : ZMod m) * (s : ZMod m)) ≠ 0 := by
        have hpos : 0 < 2 * s := by omega
        have hlt : 2 * s < m := by omega
        have hne := zmod_neg_nat_ne_zero (m := m) (n := 2 * s) hpos hlt
        intro hzero
        exact hne (by simpa [Nat.cast_mul] using hzero)
      exact p5_blockVec_ne_two_of_x_ne_zero hx0
    · have htpos : 0 < t := by omega
      have hk_eq : k = s * m + t := by
        dsimp [t]
        omega
      rw [hk_eq]
      rw [Nat.add_comm]
      rw [Function.iterate_add_apply]
      rw [hprefix_state]
      simpa [G] using normalizedG0Vec_low_tail_p5_no_earlier
        (m := m) (h := h) hm (a := a) (b := b) (s := s) hspos hsh hB
        t htpos httail

theorem zmod_mid_first_x_ne {m h k : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hk : k < h - 1) :
    ((-2 : ZMod m) - (2 : ZMod m) * (k : ZMod m)) ≠ 0 := by
  have hpos : 0 < 2 * (k + 1) := by omega
  have hlt : 2 * (k + 1) < m := by omega
  have hne := zmod_neg_nat_ne_zero (m := m) (n := 2 * (k + 1)) hpos hlt
  intro h
  apply hne
  have heq : (-(↑(2 * (k + 1)) : ZMod m)) =
      (-2 : ZMod m) - (2 : ZMod m) * (k : ZMod m) := by
    simp [Nat.cast_mul, Nat.cast_add]
    ring
  rwa [heq]

theorem normalizedG0Vec_sigma_to_neg_one_mid {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) {a b : ZMod m}
    (hhpos : 0 < h)
    (hs : a + b = (h : ZMod m)) (hB : b + 1 ≠ 0) :
    (((normalizedG0Vec (m := m))^[m])^[h]) (sigmaVec a b) =
      blockVec (-(2 : ZMod m) * (h : ZMod m)) (a + (h : ZMod m)) (b + 1) (-1) := by
  let H : Vec5 m -> Vec5 m := (normalizedG0Vec (m := m))^[m]
  let r := h - 1
  have hhm : h < m := by omega
  have hfirst : H (sigmaVec a b) = blockVec (-2) (a + 1) (b + 1) (-(h : ZMod m)) := by
    dsimp [H]
    rw [normalizedG0Vec_first_block_from_sigma hhpos hhm hs hB]
    ext i
    fin_cases i <;> simp [blockVec]
  have hdec : H^[r] (blockVec (-2) (a + 1) (b + 1) (-(h : ZMod m))) =
      blockVec ((-2 : ZMod m) - (2 : ZMod m) * (r : ZMod m))
        (a + 1 + (r : ZMod m)) (b + 1) (-(((h - r : Nat) : ZMod m))) := by
    dsimp [H]
    apply normalizedG0Vec_block_decrement_iter
    · dsimp [r]
      omega
    · exact hhm
    · exact hB
    · intro k hk
      dsimp [r] at hk
      exact zmod_mid_first_x_ne (m := m) (h := h) (k := k) hm hk
  have hiter : H^[h] (sigmaVec a b) = H^[r] (H (sigmaVec a b)) := by
    have hh_eq : h = r + 1 := by dsimp [r]; omega
    simpa [hh_eq] using (Function.iterate_succ_apply' H r (sigmaVec a b))
  rw [hiter, hfirst, hdec]
  dsimp [r]
  ext i
  fin_cases i <;> simp [blockVec]
  · rw [zmod_nat_pred_eq_sub_one (m := m) (s := h) hhpos]
    ring
  · rw [zmod_nat_pred_eq_sub_one (m := m) (s := h) hhpos]
    ring
  · rw [zmod_nat_pred_eq_sub_one (m := m) (s := h) hhpos]
    ring

theorem normalizedG0Vec_sigma_to_neg_one_mid_p5_no_earlier {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a b : ZMod m}
    (hs : a + b = (h : ZMod m)) (hB : b + 1 ≠ 0) :
    forall k : Nat, 0 < k -> k < h * m ->
      p5 (((normalizedG0Vec (m := m))^[k]) (sigmaVec a b)) ≠ 2 := by
  have hneg2 : (-2 : ZMod m) ≠ 0 := by
    simpa using zmod_neg_nat_ne_zero (m := m) (n := 2) (by omega) (by omega)
  apply normalizedG0Vec_sigma_to_neg_one_p5_no_earlier_aux
      (m := m) (a := a) (b := b) (s := h) (by omega) (by omega) hs hB hneg2
  intro k hk
  exact zmod_mid_first_x_ne (m := m) (h := h) (k := k) hm hk

theorem zmod_mid_y_ne {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) {a b : ZMod m}
    (hs : a + b = (h : ZMod m)) (hB : b + 1 ≠ 0) :
    a + (h : ZMod m) ≠ 0 := by
  intro hy
  apply hB
  have hmzero : ((2 * h + 1 : Nat) : ZMod m) = 0 := by
    rw [← hm]
    exact ZMod.natCast_self m
  have hmzero' : (2 : ZMod m) * (h : ZMod m) + 1 = 0 := by
    simpa [Nat.cast_mul, Nat.cast_add] using hmzero
  have ha : a = -(h : ZMod m) := by
    calc
      a = a + (h : ZMod m) - (h : ZMod m) := by ring
      _ = 0 - (h : ZMod m) := by rw [hy]
      _ = -(h : ZMod m) := by ring
  have hb : b = (2 : ZMod m) * (h : ZMod m) := by
    calc
      b = (a + b) - a := by ring
      _ = (h : ZMod m) - a := by rw [hs]
      _ = (h : ZMod m) - (-(h : ZMod m)) := by rw [ha]
      _ = (2 : ZMod m) * (h : ZMod m) := by ring
  rw [hb]
  exact hmzero'

theorem normalizedG0Vec_mid_neg_one_step {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hhpos : 0 < h) {a b : ZMod m} (hB : b + 1 ≠ 0) :
    ((normalizedG0Vec (m := m))^[m])
      (blockVec (-(2 : ZMod m) * (h : ZMod m)) (a + (h : ZMod m)) (b + 1) (-1)) =
      blockVec 0 (a + (h : ZMod m)) (b + 1) 0 := by
  have hx : (-(2 : ZMod m) * (h : ZMod m)) ≠ 0 := by
    have hpos : 0 < 2 * h := by omega
    have hlt : 2 * h < m := by omega
    have hne := zmod_neg_nat_ne_zero (m := m) (n := 2 * h) hpos hlt
    intro h
    exact hne (by simpa [Nat.cast_mul] using h)
  rw [normalizedG0Vec_block_neg_one hx hB]
  ext i
  fin_cases i <;> simp [blockVec]
  have hmzero : ((2 * h + 1 : Nat) : ZMod m) = 0 := by
    rw [← hm]
    exact ZMod.natCast_self m
  have hmzero' : (2 : ZMod m) * (h : ZMod m) + 1 = 0 := by
    simpa [Nat.cast_mul, Nat.cast_add] using hmzero
  linear_combination -hmzero'

theorem normalizedG0Vec_mid_zero_x_zero_step {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) {a b : ZMod m}
    (hs : a + b = (h : ZMod m)) (hB : b + 1 ≠ 0) :
    ((normalizedG0Vec (m := m))^[m])
      (blockVec 0 (a + (h : ZMod m)) (b + 1) 0) =
      blockVec (-1) (a + (h : ZMod m) + 1) (b + 1) 0 := by
  have hy := zmod_mid_y_ne (m := m) (h := h) hm hs hB
  rw [normalizedG0Vec_block_zero_of_x_zero hy hB]
  ext i
  fin_cases i <;> simp [blockVec]

theorem normalizedG0Vec_mid_zero_x_ne_zero_step {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) {a b : ZMod m} (hh2 : 2 <= h) (hB : b + 1 ≠ 0) :
    ((normalizedG0Vec (m := m))^[m])
      (blockVec (-1) (a + (h : ZMod m) + 1) (b + 1) 0) =
      blockVec (-3) (a + (h : ZMod m) + 2) (b + 1)
        (-(((m - 1 : Nat) : ZMod m))) := by
  have hx : (-1 : ZMod m) ≠ 0 := by
    simpa using zmod_neg_nat_ne_zero (m := m) (n := 1) (by omega) (by omega)
  rw [normalizedG0Vec_block_zero_of_x_ne_zero (hm := by omega) hx hB]
  ext i
  fin_cases i <;> simp [blockVec, zmod_neg_nat_pred_self_eq_one]
  all_goals ring

theorem zmod_mid_second_x_ne {m h k : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hk : k < h - 1) :
    ((-3 : ZMod m) - (2 : ZMod m) * (k : ZMod m)) ≠ 0 := by
  have hpos : 0 < 3 + 2 * k := by omega
  have hlt : 3 + 2 * k < m := by omega
  have hne := zmod_neg_nat_ne_zero (m := m) (n := 3 + 2 * k) hpos hlt
  intro h
  apply hne
  have heq : (-(↑(3 + 2 * k) : ZMod m)) =
      (-3 : ZMod m) - (2 : ZMod m) * (k : ZMod m) := by
    simp [Nat.cast_mul, Nat.cast_add]
    ring
  rwa [heq]

theorem normalizedG0Vec_mid_tail_p5_no_earlier {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a b : ZMod m}
    (hs : a + b = (h : ZMod m)) (hB : b + 1 ≠ 0) :
    forall k : Nat, 0 < k -> k < (h + 2) * m ->
      p5 (((normalizedG0Vec (m := m))^[k])
        (blockVec (-(2 : ZMod m) * (h : ZMod m)) (a + (h : ZMod m))
          (b + 1) (-1))) ≠ 2 := by
  have hm5 : 5 <= m := by omega
  let G := normalizedG0Vec (m := m)
  let y0 : ZMod m := a + (h : ZMod m)
  let B : ZMod m := b + 1
  have hx0 : (-(2 : ZMod m) * (h : ZMod m)) ≠ 0 := by
    have hpos : 0 < 2 * h := by omega
    have hlt : 2 * h < m := by omega
    have hne := zmod_neg_nat_ne_zero (m := m) (n := 2 * h) hpos hlt
    intro hzero
    exact hne (by simpa [Nat.cast_mul] using hzero)
  have hy : y0 ≠ 0 := by
    dsimp [y0]
    exact zmod_mid_y_ne (m := m) (h := h) hm hs hB
  have hneg1 : (-1 : ZMod m) ≠ 0 :=
    by simpa using zmod_neg_nat_ne_zero (m := m) (n := 1) (by omega) (by omega)
  have hneg3 : (-3 : ZMod m) ≠ 0 :=
    by simpa using zmod_neg_nat_ne_zero (m := m) (n := 3) (by omega) (by omega)
  intro k hkpos hklt
  by_cases hkfirst : k < m
  · dsimp [G, y0, B]
    exact normalizedG0Vec_block_neg_one_p5_no_earlier hx0 hB k hkpos hkfirst
  · let u := k - m
    have htail1 : u < (h + 1) * m := by
      dsimp [u]
      have hsplit : (h + 2) * m = (h + 1) * m + m := by
        have hlen : h + 2 = (h + 1) + 1 := by omega
        rw [hlen]
        rw [Nat.add_mul]
        simp
      have hklt' : k < (h + 1) * m + m := by
        simpa [hsplit] using hklt
      omega
    have hk_eq : k = m + u := by
      dsimp [u]
      omega
    rw [hk_eq]
    rw [Nat.add_comm]
    rw [Function.iterate_add_apply]
    dsimp [G, y0, B]
    rw [normalizedG0Vec_mid_neg_one_step (m := m) (h := h) hm (by omega)
      (a := a) (b := b) hB]
    by_cases hu0 : u = 0
    · simp [hu0]
      have hp := p5_blockVec_zero_zero_eq_one
        (m := m) (y := a + (h : ZMod m)) (B := b + 1) hy hB
      simpa [hp]
    · have hupos : 0 < u := by omega
      by_cases hufirst : u < m
      · exact normalizedG0Vec_block_zero_of_x_zero_p5_no_earlier
          (m := m) hy hB u hupos hufirst
      · let v := u - m
        have hvlt : v < h * m := by
          dsimp [v]
          have hsplit : (h + 1) * m = h * m + m := by
            have hlen : h + 1 = h + 1 := by omega
            rw [hlen]
            rw [Nat.add_mul]
            simp
          have hult' : u < h * m + m := by
            simpa [hsplit] using htail1
          omega
        have hu_eq : u = m + v := by
          dsimp [v]
          omega
        rw [hu_eq]
        rw [Nat.add_comm]
        rw [Function.iterate_add_apply]
        rw [normalizedG0Vec_mid_zero_x_zero_step (m := m) (h := h) hm
          (a := a) (b := b) hs hB]
        by_cases hv0 : v = 0
        · simp [hv0]
          exact p5_blockVec_ne_two_of_x_ne_zero hneg1
        · have hvpos : 0 < v := by omega
          by_cases hvfirst : v < m
          · exact normalizedG0Vec_block_zero_of_x_ne_zero_p5_no_earlier
              (m := m) hm5 hneg1 hB v hvpos hvfirst
          · let w := v - m
            have hwlt : w < (h - 1) * m := by
              dsimp [w]
              have hsplit : h * m = (h - 1) * m + m := by
                have hlen : h = (h - 1) + 1 := by omega
                rw [hlen]
                rw [Nat.add_mul]
                simp
              have hvlt' : v < (h - 1) * m + m := by
                simpa [hsplit] using hvlt
              omega
            have hv_eq : v = m + w := by
              dsimp [w]
              omega
            rw [hv_eq]
            rw [Nat.add_comm]
            rw [Function.iterate_add_apply]
            rw [normalizedG0Vec_mid_zero_x_ne_zero_step (m := m) (h := h) hm
              (a := a) (b := b) hh2 hB]
            by_cases hw0 : w = 0
            · simp [hw0]
              exact p5_blockVec_ne_two_of_x_ne_zero hneg3
            · have hwpos : 0 < w := by omega
              apply normalizedG0Vec_block_decrement_iter_p5_no_earlier
                  (m := m) (x := (-3 : ZMod m)) (y := a + (h : ZMod m) + 2)
                  (B := b + 1) (s := m - 1) (r := h - 1)
              · omega
              · omega
              · exact hB
              · intro j hj
                exact zmod_mid_second_x_ne (m := m) (h := h) (k := j) hm hj
              · exact hwpos
              · exact hwlt

theorem iterate_decomp5 {α : Type*} (f : α -> α) (x : α) (n : Nat) :
    f^[n + 3] x = f^[n] (f (f (f x))) := by
  rw [Function.iterate_add_apply]
  rfl

theorem normalizedG0Vec_first_return_mid {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a b : ZMod m}
    (hs : a + b = (h : ZMod m)) (hB : b + 1 ≠ 0) :
    (((normalizedG0Vec (m := m))^[m])^[2 * (h + 1)]) (sigmaVec a b) =
      sigmaVec a (b + 1) := by
  let H : Vec5 m -> Vec5 m := (normalizedG0Vec (m := m))^[m]
  let r2 := h - 1
  have hsigma_neg := normalizedG0Vec_sigma_to_neg_one_mid (m := m) (h := h)
    hm (by omega) (a := a) (b := b) hs hB
  have hsplit : 2 * (h + 1) = (h + 2) + h := by omega
  have hiter1 : H^[2 * (h + 1)] (sigmaVec a b) = H^[h + 2] (H^[h] (sigmaVec a b)) := by
    conv_lhs => rw [hsplit]
    rw [Function.iterate_add_apply]
  have hrem_eq : h + 2 = r2 + 3 := by dsimp [r2]; omega
  have hiter2 : H^[h + 2]
      (blockVec (-(2 : ZMod m) * (h : ZMod m)) (a + (h : ZMod m)) (b + 1) (-1)) =
      H^[r2] (H (H (H (blockVec (-(2 : ZMod m) * (h : ZMod m))
        (a + (h : ZMod m)) (b + 1) (-1))))) := by
    calc
      H^[h + 2]
          (blockVec (-(2 : ZMod m) * (h : ZMod m)) (a + (h : ZMod m)) (b + 1) (-1)) =
        H^[r2 + 3]
          (blockVec (-(2 : ZMod m) * (h : ZMod m)) (a + (h : ZMod m)) (b + 1) (-1)) := by
          rw [hrem_eq]
      _ = H^[r2] (H (H (H (blockVec (-(2 : ZMod m) * (h : ZMod m))
        (a + (h : ZMod m)) (b + 1) (-1))))) := by
        simpa using (iterate_decomp5 H
          (blockVec (-(2 : ZMod m) * (h : ZMod m)) (a + (h : ZMod m)) (b + 1) (-1))
          r2)
  rw [hiter1, hsigma_neg, hiter2]
  change ((normalizedG0Vec (m := m))^[m])^[r2]
      (((normalizedG0Vec (m := m))^[m])
        (((normalizedG0Vec (m := m))^[m])
          (((normalizedG0Vec (m := m))^[m])
            (blockVec (-(2 : ZMod m) * (h : ZMod m)) (a + (h : ZMod m))
              (b + 1) (-1))))) =
    sigmaVec a (b + 1)
  rw [normalizedG0Vec_mid_neg_one_step (m := m) (h := h) hm (by omega)
    (a := a) (b := b) hB]
  rw [normalizedG0Vec_mid_zero_x_zero_step (m := m) (h := h) hm (a := a) (b := b) hs hB]
  rw [normalizedG0Vec_mid_zero_x_ne_zero_step (m := m) (h := h) hm (a := a) (b := b)
    hh2 hB]
  have hdec2 : ((normalizedG0Vec (m := m))^[m])^[r2]
      (blockVec (-3) (a + (h : ZMod m) + 2) (b + 1)
        (-(((m - 1 : Nat) : ZMod m)))) =
      blockVec ((-3 : ZMod m) - (2 : ZMod m) * (r2 : ZMod m))
        (a + (h : ZMod m) + 2 + (r2 : ZMod m)) (b + 1)
        (-(((m - 1 - r2 : Nat) : ZMod m))) := by
    apply normalizedG0Vec_block_decrement_iter
    · dsimp [r2]
      omega
    · omega
    · exact hB
    · intro k hk
      dsimp [r2] at hk
      exact zmod_mid_second_x_ne (m := m) (h := h) (k := k) hm hk
  rw [hdec2]
  ext i
  fin_cases i <;> simp [blockVec, sigmaVec]
  · have hmzero : ((2 * h + 1 : Nat) : ZMod m) = 0 := by
      rw [← hm]
      exact ZMod.natCast_self m
    have hmzero' : (2 : ZMod m) * (h : ZMod m) + 1 = 0 := by
      simpa [Nat.cast_mul, Nat.cast_add] using hmzero
    rw [zmod_nat_pred_eq_sub_one (m := m) (s := h) (by omega)]
    linear_combination -hmzero'
  · have hmzero : ((2 * h + 1 : Nat) : ZMod m) = 0 := by
      rw [← hm]
      exact ZMod.natCast_self m
    have hmzero' : (2 : ZMod m) * (h : ZMod m) + 1 = 0 := by
      simpa [Nat.cast_mul, Nat.cast_add] using hmzero
    rw [zmod_nat_pred_eq_sub_one (m := m) (s := h) (by omega)]
    linear_combination hmzero'
  · have hmsub : m - 1 - r2 = h + 1 := by dsimp [r2]; omega
    rw [hmsub]
    simp [Nat.cast_add]
    rw [← hs]
    ring

theorem normalizedG0Vec_first_return_mid_p5_no_earlier {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a b : ZMod m}
    (hs : a + b = (h : ZMod m)) (hB : b + 1 ≠ 0) :
    forall k : Nat, 0 < k -> k < 2 * (h + 1) * m ->
      p5 (((normalizedG0Vec (m := m))^[k]) (sigmaVec a b)) ≠ 2 := by
  intro k hkpos hklt
  let G := normalizedG0Vec (m := m)
  change p5 (G^[k] (sigmaVec a b)) ≠ 2
  by_cases hkprefix : k < h * m
  · simpa [G] using normalizedG0Vec_sigma_to_neg_one_mid_p5_no_earlier
      (m := m) (h := h) hm hh2 (a := a) (b := b) hs hB k hkpos hkprefix
  · let t := k - h * m
    have httail : t < (h + 2) * m := by
      dsimp [t]
      have hsplit : 2 * (h + 1) * m = h * m + (h + 2) * m := by
        have hlen : 2 * (h + 1) = h + (h + 2) := by omega
        rw [hlen]
        rw [Nat.add_mul]
      have hklt' : k < h * m + (h + 2) * m := by
        simpa [hsplit] using hklt
      omega
    have hprefix_state :
        G^[h * m] (sigmaVec a b) =
          blockVec (-(2 : ZMod m) * (h : ZMod m)) (a + (h : ZMod m))
            (b + 1) (-1) := by
      dsimp [G]
      rw [Nat.mul_comm h m]
      rw [Function.iterate_mul]
      exact normalizedG0Vec_sigma_to_neg_one_mid (m := m) (h := h)
        hm (by omega) (a := a) (b := b) hs hB
    by_cases ht0 : t = 0
    · have hk_eq : k = h * m := by
        dsimp [t] at ht0
        omega
      rw [hk_eq, hprefix_state]
      have hx0 : (-(2 : ZMod m) * (h : ZMod m)) ≠ 0 := by
        have hpos : 0 < 2 * h := by omega
        have hlt : 2 * h < m := by omega
        have hne := zmod_neg_nat_ne_zero (m := m) (n := 2 * h) hpos hlt
        intro hzero
        exact hne (by simpa [Nat.cast_mul] using hzero)
      exact p5_blockVec_ne_two_of_x_ne_zero hx0
    · have htpos : 0 < t := by omega
      have hk_eq : k = h * m + t := by
        dsimp [t]
        omega
      rw [hk_eq]
      rw [Nat.add_comm]
      rw [Function.iterate_add_apply]
      rw [hprefix_state]
      simpa [G] using normalizedG0Vec_mid_tail_p5_no_earlier
        (m := m) (h := h) hm hh2 (a := a) (b := b) hs hB t htpos httail

theorem zmod_odd_two_mul_nat_ne_zero {m h n : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hnpos : 0 < n) (hnm : n < m) :
    (((2 * n : Nat) : ZMod m)) ≠ 0 := by
  intro hz
  have hd : m ∣ 2 * n := (ZMod.natCast_eq_zero_iff (2 * n) m).mp hz
  have hodd : Odd m := ⟨h, hm⟩
  have hcop : Nat.Coprime m 2 := Nat.coprime_two_right.mpr hodd
  have hdn : m ∣ n := (Nat.Coprime.dvd_mul_left (m := 2) (n := n) (k := m) hcop).1 hd
  exact (Nat.not_dvd_of_pos_of_lt hnpos hnm) hdn

theorem zmod_odd_first_x_ne {m h s k : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hk : k < s - 1) (hsm : s < m) :
    ((-2 : ZMod m) - (2 : ZMod m) * (k : ZMod m)) ≠ 0 := by
  have hne := zmod_odd_two_mul_nat_ne_zero (m := m) (h := h) (n := k + 1) hm
    (by omega) (by omega)
  intro h
  apply hne
  have hneg : (-(↑(2 * (k + 1)) : ZMod m)) = 0 := by
    have heq : (-(↑(2 * (k + 1)) : ZMod m)) =
        (-2 : ZMod m) - (2 : ZMod m) * (k : ZMod m) := by
      simp [Nat.cast_mul, Nat.cast_add]
      ring
    rwa [heq]
  exact neg_eq_zero.mp hneg

theorem normalizedG0Vec_sigma_to_neg_one_high {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) {a b : ZMod m} {s : Nat}
    (hspos : 0 < s) (hsm : s < m)
    (hs : a + b = (s : ZMod m)) (hB : b + 1 ≠ 0) :
    (((normalizedG0Vec (m := m))^[m])^[s]) (sigmaVec a b) =
      blockVec (-(2 : ZMod m) * (s : ZMod m)) (a + (s : ZMod m)) (b + 1) (-1) := by
  let H : Vec5 m -> Vec5 m := (normalizedG0Vec (m := m))^[m]
  let r := s - 1
  have hfirst : H (sigmaVec a b) = blockVec (-2) (a + 1) (b + 1) (-(s : ZMod m)) := by
    dsimp [H]
    rw [normalizedG0Vec_first_block_from_sigma hspos hsm hs hB]
    ext i
    fin_cases i <;> simp [blockVec]
  have hdec : H^[r] (blockVec (-2) (a + 1) (b + 1) (-(s : ZMod m))) =
      blockVec ((-2 : ZMod m) - (2 : ZMod m) * (r : ZMod m))
        (a + 1 + (r : ZMod m)) (b + 1) (-(((s - r : Nat) : ZMod m))) := by
    dsimp [H]
    apply normalizedG0Vec_block_decrement_iter
    · dsimp [r]
      omega
    · exact hsm
    · exact hB
    · intro k hk
      dsimp [r] at hk
      exact zmod_odd_first_x_ne (m := m) (h := h) (s := s) (k := k) hm hk hsm
  have hiter : H^[s] (sigmaVec a b) = H^[r] (H (sigmaVec a b)) := by
    have hs_eq : s = r + 1 := by dsimp [r]; omega
    simpa [hs_eq] using (Function.iterate_succ_apply' H r (sigmaVec a b))
  rw [hiter, hfirst, hdec]
  dsimp [r]
  ext i
  fin_cases i <;> simp [blockVec]
  · rw [zmod_nat_pred_eq_sub_one (m := m) (s := s) hspos]
    ring
  · rw [zmod_nat_pred_eq_sub_one (m := m) (s := s) hspos]
    ring
  · rw [zmod_nat_pred_eq_sub_one (m := m) (s := s) hspos]
    ring

theorem normalizedG0Vec_sigma_to_neg_one_high_p5_no_earlier {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) {a b : ZMod m} {s : Nat}
    (hspos : 0 < s) (hsm : s < m)
    (hs : a + b = (s : ZMod m)) (hB : b + 1 ≠ 0) :
    forall k : Nat, 0 < k -> k < s * m ->
      p5 (((normalizedG0Vec (m := m))^[k]) (sigmaVec a b)) ≠ 2 := by
  have hneg2 : (-2 : ZMod m) ≠ 0 := by
    simpa using zmod_neg_nat_ne_zero (m := m) (n := 2) (by omega) (by omega)
  apply normalizedG0Vec_sigma_to_neg_one_p5_no_earlier_aux
      (m := m) (a := a) (b := b) (s := s) hspos hsm hs hB hneg2
  intro k hk
  exact zmod_odd_first_x_ne (m := m) (h := h) (s := s) (k := k) hm hk hsm

theorem normalizedG0Vec_high_neg_one_step {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) {a b : ZMod m} {s : Nat}
    (hspos : 0 < s) (hsm : s < m) (hB : b + 1 ≠ 0) :
    ((normalizedG0Vec (m := m))^[m])
      (blockVec (-(2 : ZMod m) * (s : ZMod m)) (a + (s : ZMod m)) (b + 1) (-1)) =
      blockVec ((-2 : ZMod m) * (s : ZMod m) - 1) (a + (s : ZMod m))
        (b + 1) 0 := by
  have hx : (-(2 : ZMod m) * (s : ZMod m)) ≠ 0 := by
    have hne := zmod_odd_two_mul_nat_ne_zero (m := m) (h := h) (n := s) hm hspos hsm
    intro h
    apply hne
    have hneg : (-(↑(2 * s) : ZMod m)) = 0 := by
      simpa [Nat.cast_mul] using h
    exact neg_eq_zero.mp hneg
  rw [normalizedG0Vec_block_neg_one hx hB]
  ext i
  fin_cases i <;> simp [blockVec]

theorem zmod_high_zero_x_ne {m h s : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hhs : h < s) (hsm : s < m) :
    ((-2 : ZMod m) * (s : ZMod m) - 1) ≠ 0 := by
  let n := 2 * s + 1
  have hn_gt_m : m < n := by dsimp [n]; omega
  have hn_lt_2m : n < 2 * m := by dsimp [n]; omega
  intro hzero
  have hcast : ((n : Nat) : ZMod m) = 0 := by
    have hneg : (-(n : ZMod m)) = 0 := by
      have heq : (-(n : ZMod m)) = (-2 : ZMod m) * (s : ZMod m) - 1 := by
        dsimp [n]
        simp [Nat.cast_mul, Nat.cast_add]
        ring
      rwa [heq]
    exact neg_eq_zero.mp hneg
  have hd : m ∣ n := (ZMod.natCast_eq_zero_iff n m).mp hcast
  rcases hd with ⟨q, hq⟩
  have hq2 : q < 2 := by
    apply Nat.lt_of_mul_lt_mul_right (a := m)
    calc
      q * m = m * q := by rw [mul_comm]
      _ = n := hq.symm
      _ < 2 * m := hn_lt_2m
  interval_cases q <;> omega

theorem normalizedG0Vec_high_zero_step {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) {a b : ZMod m} {s : Nat}
    (hh2 : 2 <= h) (hhs : h < s) (hsm : s < m) (hB : b + 1 ≠ 0) :
    ((normalizedG0Vec (m := m))^[m])
      (blockVec ((-2 : ZMod m) * (s : ZMod m) - 1) (a + (s : ZMod m)) (b + 1) 0) =
      blockVec ((-2 : ZMod m) * (s : ZMod m) - 3) (a + (s : ZMod m) + 1)
        (b + 1) (-(((m - 1 : Nat) : ZMod m))) := by
  have hx := zmod_high_zero_x_ne (m := m) (h := h) (s := s) hm hhs hsm
  rw [normalizedG0Vec_block_zero_of_x_ne_zero (hm := by omega) hx hB]
  ext i
  fin_cases i <;> simp [blockVec, zmod_neg_nat_pred_self_eq_one]
  all_goals ring

theorem zmod_high_second_x_ne {m h s k : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hhs : h < s) (_hsm : s < m) (hk : k < 3 * h - s) :
    ((-2 : ZMod m) * (s : ZMod m) - 3 - (2 : ZMod m) * (k : ZMod m)) ≠ 0 := by
  let n := 2 * s + 3 + 2 * k
  have hn_gt_m : m < n := by dsimp [n]; omega
  have hn_lt_3m : n < 3 * m := by dsimp [n]; omega
  have hn_not_two : ¬2 ∣ n := by
    have hnot := Nat.not_two_dvd_bit1 (s + k + 1)
    have hn_eq : n = 2 * (s + k + 1) + 1 := by dsimp [n]; omega
    rwa [hn_eq]
  intro h
  have hcast : ((n : Nat) : ZMod m) = 0 := by
    have hneg : (-(n : ZMod m)) = 0 := by
      have heq : (-(n : ZMod m)) =
          (-2 : ZMod m) * (s : ZMod m) - 3 - (2 : ZMod m) * (k : ZMod m) := by
        dsimp [n]
        simp [Nat.cast_add, Nat.cast_mul]
        ring
      rwa [heq]
    exact neg_eq_zero.mp hneg
  have hd : m ∣ n := (ZMod.natCast_eq_zero_iff n m).mp hcast
  rcases hd with ⟨q, hq⟩
  have hq3 : q < 3 := by
    apply Nat.lt_of_mul_lt_mul_right (a := m)
    calc
      q * m = m * q := by rw [mul_comm]
      _ = n := hq.symm
      _ < 3 * m := hn_lt_3m
  interval_cases q
  · omega
  · omega
  · have h2dvd : 2 ∣ n := by
      rw [hq, mul_comm]
      exact dvd_mul_right 2 m
    exact hn_not_two h2dvd

theorem normalizedG0Vec_high_tail_p5_no_earlier {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) {a b : ZMod m} {s : Nat}
    (hh2 : 2 <= h) (hspos : 0 < s) (hhs : h < s) (hsm : s < m)
    (hB : b + 1 ≠ 0) :
    forall k : Nat, 0 < k -> k < (3 * h + 2 - s) * m ->
      p5 (((normalizedG0Vec (m := m))^[k])
        (blockVec (-(2 : ZMod m) * (s : ZMod m)) (a + (s : ZMod m))
          (b + 1) (-1))) ≠ 2 := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hm5 : 5 <= m := by omega
  let G := normalizedG0Vec (m := m)
  let x0 : ZMod m := -(2 : ZMod m) * (s : ZMod m)
  let y0 : ZMod m := a + (s : ZMod m)
  let B : ZMod m := b + 1
  have hx0 : x0 ≠ 0 := by
    dsimp [x0]
    have hne := zmod_odd_two_mul_nat_ne_zero (m := m) (h := h) (n := s) hm hspos hsm
    intro hzero
    apply hne
    have hneg : (-(↑(2 * s) : ZMod m)) = 0 := by
      simpa [Nat.cast_mul] using hzero
    exact neg_eq_zero.mp hneg
  have hx1 : (-2 : ZMod m) * (s : ZMod m) - 1 ≠ 0 :=
    zmod_high_zero_x_ne (m := m) (h := h) (s := s) hm hhs hsm
  have hx1n : -((2 : ZMod m) * (s : ZMod m)) - 1 ≠ 0 := by
    intro hzero
    apply hx1
    have heq : (-2 : ZMod m) * (s : ZMod m) - 1 =
        -((2 : ZMod m) * (s : ZMod m)) - 1 := by ring
    rwa [heq]
  intro k hkpos hklt
  by_cases hkfirst : k < m
  · dsimp [G, x0, y0, B]
    exact normalizedG0Vec_block_neg_one_p5_no_earlier hx0 hB k hkpos hkfirst
  · let u := k - m
    have htail1 : u < (3 * h + 1 - s) * m := by
      dsimp [u]
      have hsplit : (3 * h + 2 - s) * m = (3 * h + 1 - s) * m + m := by
        have hlen : 3 * h + 2 - s = (3 * h + 1 - s) + 1 := by omega
        rw [hlen]
        rw [Nat.add_mul]
        simp
      have hklt' : k < (3 * h + 1 - s) * m + m := by
        simpa [hsplit] using hklt
      omega
    have hk_eq : k = m + u := by
      dsimp [u]
      omega
    rw [hk_eq]
    rw [Nat.add_comm]
    rw [Function.iterate_add_apply]
    dsimp [G, x0, y0, B]
    rw [normalizedG0Vec_high_neg_one_step (m := m) (h := h) hm
      (a := a) (b := b) (s := s) hspos hsm hB]
    by_cases hu0 : u = 0
    · simp [hu0]
      exact p5_blockVec_ne_two_of_x_ne_zero hx1n
    · have hupos : 0 < u := by omega
      by_cases hufirst : u < m
      · exact normalizedG0Vec_block_zero_of_x_ne_zero_p5_no_earlier
          (m := m) hm5 hx1 hB u hupos hufirst
      · let v := u - m
        have hvlt : v < (3 * h - s) * m := by
          dsimp [v]
          have hsplit : (3 * h + 1 - s) * m = (3 * h - s) * m + m := by
            have hlen : 3 * h + 1 - s = (3 * h - s) + 1 := by omega
            rw [hlen]
            rw [Nat.add_mul]
            simp
          have hult' : u < (3 * h - s) * m + m := by
            simpa [hsplit] using htail1
          omega
        by_cases hv0 : v = 0
        · have hu_eq : u = m := by
            dsimp [v] at hv0
            omega
          rw [hu_eq]
          rw [normalizedG0Vec_high_zero_step (m := m) (h := h) hm
            (a := a) (b := b) (s := s) hh2 hhs hsm hB]
          have hx2 : (-2 : ZMod m) * (s : ZMod m) - 3 ≠ 0 := by
            simpa using zmod_high_second_x_ne (m := m) (h := h) (s := s) (k := 0)
              hm hhs hsm (by omega)
          exact p5_blockVec_ne_two_of_x_ne_zero hx2
        · have hvpos : 0 < v := by omega
          have hu_eq : u = m + v := by
            dsimp [v]
            omega
          rw [hu_eq]
          rw [Nat.add_comm]
          rw [Function.iterate_add_apply]
          rw [normalizedG0Vec_high_zero_step (m := m) (h := h) hm
            (a := a) (b := b) (s := s) hh2 hhs hsm hB]
          apply normalizedG0Vec_block_decrement_iter_p5_no_earlier
              (m := m) (x := (-2 : ZMod m) * (s : ZMod m) - 3)
              (y := a + (s : ZMod m) + 1) (B := b + 1)
              (s := m - 1) (r := 3 * h - s)
          · omega
          · omega
          · exact hB
          · intro j hj
            exact zmod_high_second_x_ne (m := m) (h := h) (s := s) (k := j)
              hm hhs hsm hj
          · exact hvpos
          · exact hvlt

theorem normalizedG0Vec_first_return_high {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) {a b : ZMod m} {s : Nat}
    (hh2 : 2 <= h) (hspos : 0 < s) (hhs : h < s) (hsm : s < m)
    (hs : a + b = (s : ZMod m)) (hB : b + 1 ≠ 0) :
    (((normalizedG0Vec (m := m))^[m])^[3 * h + 2]) (sigmaVec a b) =
      sigmaVec (a + (h : ZMod m)) (b + 1) := by
  let H : Vec5 m -> Vec5 m := (normalizedG0Vec (m := m))^[m]
  let r2 := 3 * h - s
  have hsigma_neg := normalizedG0Vec_sigma_to_neg_one_high (m := m) (h := h)
    hm hspos hsm hs hB
  have hsplit : 3 * h + 2 = (3 * h + 2 - s) + s := by omega
  have hiter1 : H^[3 * h + 2] (sigmaVec a b) =
      H^[3 * h + 2 - s] (H^[s] (sigmaVec a b)) := by
    conv_lhs => rw [hsplit]
    rw [Function.iterate_add_apply]
  have hrem_eq : 3 * h + 2 - s = r2 + 2 := by dsimp [r2]; omega
  have hiter2 : H^[3 * h + 2 - s]
      (blockVec (-(2 : ZMod m) * (s : ZMod m)) (a + (s : ZMod m)) (b + 1) (-1)) =
      H^[r2] (H (H (blockVec (-(2 : ZMod m) * (s : ZMod m))
        (a + (s : ZMod m)) (b + 1) (-1)))) := by
    calc
      H^[3 * h + 2 - s]
          (blockVec (-(2 : ZMod m) * (s : ZMod m)) (a + (s : ZMod m)) (b + 1) (-1)) =
        H^[r2 + 2]
          (blockVec (-(2 : ZMod m) * (s : ZMod m)) (a + (s : ZMod m)) (b + 1) (-1)) := by
          rw [hrem_eq]
      _ = H^[r2] (H (H (blockVec (-(2 : ZMod m) * (s : ZMod m))
        (a + (s : ZMod m)) (b + 1) (-1)))) := by
        simpa using (iterate_decomp4 H
          (blockVec (-(2 : ZMod m) * (s : ZMod m)) (a + (s : ZMod m)) (b + 1) (-1))
          0 r2)
  rw [hiter1, hsigma_neg, hiter2]
  change ((normalizedG0Vec (m := m))^[m])^[r2]
      (((normalizedG0Vec (m := m))^[m])
        (((normalizedG0Vec (m := m))^[m])
          (blockVec (-(2 : ZMod m) * (s : ZMod m)) (a + (s : ZMod m))
            (b + 1) (-1)))) =
    sigmaVec (a + (h : ZMod m)) (b + 1)
  rw [normalizedG0Vec_high_neg_one_step (m := m) (h := h) hm
    (a := a) (b := b) (s := s) hspos hsm hB]
  rw [normalizedG0Vec_high_zero_step (m := m) (h := h) hm
    (a := a) (b := b) (s := s) hh2 hhs hsm hB]
  have hdec2 : ((normalizedG0Vec (m := m))^[m])^[r2]
      (blockVec ((-2 : ZMod m) * (s : ZMod m) - 3)
        (a + (s : ZMod m) + 1) (b + 1) (-(((m - 1 : Nat) : ZMod m)))) =
      blockVec (((-2 : ZMod m) * (s : ZMod m) - 3) - (2 : ZMod m) * (r2 : ZMod m))
        (a + (s : ZMod m) + 1 + (r2 : ZMod m)) (b + 1)
        (-(((m - 1 - r2 : Nat) : ZMod m))) := by
    apply normalizedG0Vec_block_decrement_iter
    · dsimp [r2]
      omega
    · omega
    · exact hB
    · intro k hk
      dsimp [r2] at hk
      exact zmod_high_second_x_ne (m := m) (h := h) (s := s) (k := k) hm hhs hsm hk
  rw [hdec2]
  have hmzero : ((2 * h + 1 : Nat) : ZMod m) = 0 := by
    rw [← hm]
    exact ZMod.natCast_self m
  have hmzero' : (2 : ZMod m) * (h : ZMod m) + 1 = 0 := by
    simpa [Nat.cast_mul, Nat.cast_add] using hmzero
  have hr2cast : ((r2 : Nat) : ZMod m) = (3 : ZMod m) * (h : ZMod m) - (s : ZMod m) := by
    dsimp [r2]
    rw [Nat.cast_sub (by omega)]
    simp [Nat.cast_mul]
  ext i
  fin_cases i <;> simp [blockVec, sigmaVec]
  · rw [hr2cast]
    linear_combination -3 * hmzero'
  · rw [hr2cast]
    linear_combination hmzero'
  · have hmsub : m - 1 - r2 = s - h := by dsimp [r2]; omega
    rw [hmsub]
    rw [Nat.cast_sub (by omega)]
    rw [← hs]
    linear_combination hmzero'

theorem normalizedG0Vec_first_return_high_p5_no_earlier {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) {a b : ZMod m} {s : Nat}
    (hh2 : 2 <= h) (hspos : 0 < s) (hhs : h < s) (hsm : s < m)
    (hs : a + b = (s : ZMod m)) (hB : b + 1 ≠ 0) :
    forall k : Nat, 0 < k -> k < (3 * h + 2) * m ->
      p5 (((normalizedG0Vec (m := m))^[k]) (sigmaVec a b)) ≠ 2 := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  intro k hkpos hklt
  let G := normalizedG0Vec (m := m)
  change p5 (G^[k] (sigmaVec a b)) ≠ 2
  by_cases hkprefix : k < s * m
  · simpa [G] using normalizedG0Vec_sigma_to_neg_one_high_p5_no_earlier
      (m := m) (h := h) hm (a := a) (b := b) (s := s) hspos hsm hs hB
      k hkpos hkprefix
  · let t := k - s * m
    have httail : t < (3 * h + 2 - s) * m := by
      dsimp [t]
      have hsplit : (3 * h + 2) * m = s * m + (3 * h + 2 - s) * m := by
        have hlen : 3 * h + 2 = s + (3 * h + 2 - s) := by omega
        rw [hlen]
        rw [Nat.add_mul]
        simp
      have hklt' : k < s * m + (3 * h + 2 - s) * m := by
        simpa [hsplit] using hklt
      omega
    have hprefix_state :
        G^[s * m] (sigmaVec a b) =
          blockVec (-(2 : ZMod m) * (s : ZMod m)) (a + (s : ZMod m))
            (b + 1) (-1) := by
      dsimp [G]
      rw [Nat.mul_comm s m]
      rw [Function.iterate_mul]
      exact normalizedG0Vec_sigma_to_neg_one_high (m := m) (h := h)
        hm (a := a) (b := b) (s := s) hspos hsm hs hB
    by_cases ht0 : t = 0
    · have hk_eq : k = s * m := by
        dsimp [t] at ht0
        omega
      rw [hk_eq, hprefix_state]
      have hx0 : (-(2 : ZMod m) * (s : ZMod m)) ≠ 0 := by
        have hne := zmod_odd_two_mul_nat_ne_zero (m := m) (h := h) (n := s) hm hspos hsm
        intro hzero
        apply hne
        have hneg : (-(↑(2 * s) : ZMod m)) = 0 := by
          simpa [Nat.cast_mul] using hzero
        exact neg_eq_zero.mp hneg
      exact p5_blockVec_ne_two_of_x_ne_zero hx0
    · have htpos : 0 < t := by omega
      have hk_eq : k = s * m + t := by
        dsimp [t]
        omega
      rw [hk_eq]
      rw [Nat.add_comm]
      rw [Function.iterate_add_apply]
      rw [hprefix_state]
      simpa [G] using normalizedG0Vec_high_tail_p5_no_earlier
        (m := m) (h := h) hm (a := a) (b := b) (s := s) hh2 hspos hhs hsm hB
        t htpos httail

theorem zmod_val_eq_of_eq_nat_lt {m s : Nat} [NeZero m] {x : ZMod m}
    (hs : s < m) (hx : x = (s : ZMod m)) :
    x.val = s := by
  rw [hx]
  exact ZMod.val_natCast_of_lt hs

theorem zmod_normal_low_sum_ne_zero {m h s : Nat} [NeZero m]
    (hm : m = 2 * h + 1) {a b : ZMod m}
    (hsh : s < h) (hs : a + b = (s : ZMod m)) :
    a + b + ((h + 1 : Nat) : ZMod m) ≠ 0 := by
  have hne : (((s + (h + 1) : Nat) : ZMod m)) ≠ 0 := by
    apply zmod_nat_ne_zero (m := m) (k := s + (h + 1)) <;> omega
  intro hzero
  apply hne
  calc
    (((s + (h + 1) : Nat) : ZMod m))
        = (s : ZMod m) + ((h + 1 : Nat) : ZMod m) := by
          simp [Nat.cast_add]
    _ = a + b + ((h + 1 : Nat) : ZMod m) := by rw [← hs]
    _ = 0 := hzero

theorem zmod_normal_mid_sum_zero {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) {a b : ZMod m}
    (hs : a + b = (h : ZMod m)) :
    a + b + ((h + 1 : Nat) : ZMod m) = 0 := by
  have hmzero : ((2 * h + 1 : Nat) : ZMod m) = 0 := by
    rw [← hm]
    exact ZMod.natCast_self m
  have hmzero' : (2 : ZMod m) * (h : ZMod m) + 1 = 0 := by
    simpa [Nat.cast_add, Nat.cast_mul] using hmzero
  rw [hs]
  rw [show ((h + 1 : Nat) : ZMod m) = (h : ZMod m) + 1 by simp [Nat.cast_add]]
  linear_combination hmzero'

theorem zmod_normal_high_sum_ne_zero {m h s : Nat} [NeZero m]
    (hm : m = 2 * h + 1) {a b : ZMod m}
    (hhs : h < s) (hsm : s < m) (hs : a + b = (s : ZMod m)) :
    a + b + ((h + 1 : Nat) : ZMod m) ≠ 0 := by
  let n := s + (h + 1)
  have hn_gt_m : m < n := by dsimp [n]; omega
  have hn_lt_2m : n < 2 * m := by dsimp [n]; omega
  intro hzero
  have hcast : ((n : Nat) : ZMod m) = 0 := by
    calc
      ((n : Nat) : ZMod m)
          = (s : ZMod m) + ((h + 1 : Nat) : ZMod m) := by
            dsimp [n]
            simp [Nat.cast_add]
      _ = a + b + ((h + 1 : Nat) : ZMod m) := by rw [← hs]
      _ = 0 := hzero
  have hd : m ∣ n := (ZMod.natCast_eq_zero_iff n m).mp hcast
  rcases hd with ⟨q, hq⟩
  have hq2 : q < 2 := by
    apply Nat.lt_of_mul_lt_mul_right (a := m)
    calc
      q * m = m * q := by rw [mul_comm]
      _ = n := hq.symm
      _ < 2 * m := hn_lt_2m
  interval_cases q <;> omega

theorem returnTimeSigma_nonlast_low {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a b : ZMod m} {s : Nat}
    (hab : a + b ≠ 0) (hspos : 0 < s) (hsh : s < h)
    (hs : a + b = (s : ZMod m)) (hB : b + 1 ≠ 0) :
    returnTimeSigma hm hh2 ⟨(a, b), hab⟩ = (h + 1) * m := by
  have hsval : (a + b).val = s :=
    zmod_val_eq_of_eq_nat_lt (m := m) (s := s) (by omega) hs
  simp [returnTimeSigma, hB, hsval, hsh]

theorem returnTimeSigma_nonlast_mid {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a b : ZMod m}
    (hab : a + b ≠ 0) (hs : a + b = (h : ZMod m)) (hB : b + 1 ≠ 0) :
    returnTimeSigma hm hh2 ⟨(a, b), hab⟩ = 2 * (h + 1) * m := by
  have hsval : (a + b).val = h :=
    zmod_val_eq_of_eq_nat_lt (m := m) (s := h) (by omega) hs
  simp [returnTimeSigma, hB, hsval]

theorem returnTimeSigma_nonlast_high {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a b : ZMod m} {s : Nat}
    (hab : a + b ≠ 0) (hhs : h < s) (hsm : s < m)
    (hs : a + b = (s : ZMod m)) (hB : b + 1 ≠ 0) :
    returnTimeSigma hm hh2 ⟨(a, b), hab⟩ = (3 * h + 2) * m := by
  have hsval : (a + b).val = s :=
    zmod_val_eq_of_eq_nat_lt (m := m) (s := s) hsm hs
  simp [returnTimeSigma, hB, hsval, hhs.not_gt, hhs.ne']

theorem nextSigma_nonlast_low {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a b : ZMod m} {s : Nat}
    (hab : a + b ≠ 0) (hsh : s < h)
    (hs : a + b = (s : ZMod m)) (hB : b + 1 ≠ 0) :
    nextSigma hm hh2 ⟨(a, b), hab⟩ =
      ⟨(a + (h : ZMod m), b + 1),
        by
          have hz := zmod_normal_low_sum_ne_zero (m := m) (h := h) (s := s) hm hsh hs
          intro hsum
          apply hz
          rw [show ((h + 1 : Nat) : ZMod m) = (h : ZMod m) + 1 by simp [Nat.cast_add]]
          simpa [add_assoc, add_comm, add_left_comm] using hsum⟩ := by
  apply Subtype.ext
  have hz := zmod_normal_low_sum_ne_zero (m := m) (h := h) (s := s) hm hsh hs
  have hif : ¬ (a + b + ((h : ZMod m) + 1) = 0) := by
    intro hzero
    apply hz
    rw [show ((h + 1 : Nat) : ZMod m) = (h : ZMod m) + 1 by simp [Nat.cast_add]]
    exact hzero
  simp [nextSigma, hB, Nat.cast_add]
  rw [dif_neg hif]
  ext <;> simp [Nat.cast_add] <;> ring

theorem nextSigma_nonlast_mid {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a b : ZMod m}
    (hab : a + b ≠ 0) (hs : a + b = (h : ZMod m)) (hB : b + 1 ≠ 0) :
    nextSigma hm hh2 ⟨(a, b), hab⟩ =
      ⟨(a, b + 1),
        by
          intro hsum
          apply zmod_h_add_one_ne_zero hm hh2
          have hsum' : a + b + 1 = 0 := by
            simpa [add_assoc, add_comm, add_left_comm] using hsum
          have hc : (h : ZMod m) + 1 = 0 := by
            rw [← hs]
            exact hsum'
          simpa [Nat.cast_add] using hc⟩ := by
  apply Subtype.ext
  have hz := zmod_normal_mid_sum_zero (m := m) (h := h) hm hs
  have hif : a + b + ((h : ZMod m) + 1) = 0 := by
    rw [show a + b + ((h : ZMod m) + 1) =
        a + b + ((h + 1 : Nat) : ZMod m) by simp [Nat.cast_add]]
    exact hz
  have ha : (h : ZMod m) - b = a := by
    calc
      (h : ZMod m) - b = (a + b) - b := by rw [← hs]
      _ = a := by ring
  simp [nextSigma, hB, Nat.cast_add]
  rw [dif_pos hif]
  simp [ha]

theorem nextSigma_nonlast_high {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a b : ZMod m} {s : Nat}
    (hab : a + b ≠ 0) (hhs : h < s) (hsm : s < m)
    (hs : a + b = (s : ZMod m)) (hB : b + 1 ≠ 0) :
    nextSigma hm hh2 ⟨(a, b), hab⟩ =
      ⟨(a + (h : ZMod m), b + 1),
        by
          have hz := zmod_normal_high_sum_ne_zero (m := m) (h := h) (s := s) hm hhs hsm hs
          intro hsum
          apply hz
          rw [show ((h + 1 : Nat) : ZMod m) = (h : ZMod m) + 1 by simp [Nat.cast_add]]
          simpa [add_assoc, add_comm, add_left_comm] using hsum⟩ := by
  apply Subtype.ext
  have hz := zmod_normal_high_sum_ne_zero (m := m) (h := h) (s := s) hm hhs hsm hs
  have hif : ¬ (a + b + ((h : ZMod m) + 1) = 0) := by
    intro hzero
    apply hz
    rw [show ((h + 1 : Nat) : ZMod m) = (h : ZMod m) + 1 by simp [Nat.cast_add]]
    exact hzero
  simp [nextSigma, hB, Nat.cast_add]
  rw [dif_neg hif]
  ext <;> simp [Nat.cast_add] <;> ring

theorem normalizedG0Vec_first_return_sigma_nonlast_low {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a b : ZMod m} {s : Nat}
    (hab : a + b ≠ 0) (hspos : 0 < s) (hsh : s < h)
    (hs : a + b = (s : ZMod m)) (hB : b + 1 ≠ 0) :
    ((normalizedG0Vec (m := m))^[returnTimeSigma hm hh2 ⟨(a, b), hab⟩])
        (sigmaVec a b) =
      sigmaVec
        (nextSigma hm hh2 ⟨(a, b), hab⟩).1.1
        (nextSigma hm hh2 ⟨(a, b), hab⟩).1.2 := by
  rw [returnTimeSigma_nonlast_low hm hh2 hab hspos hsh hs hB]
  rw [nextSigma_nonlast_low hm hh2 hab hsh hs hB]
  simp
  rw [Nat.mul_comm (h + 1) m]
  rw [Function.iterate_mul]
  exact normalizedG0Vec_first_return_low (m := m) (h := h) hm
    (a := a) (b := b) (s := s) hspos hsh hs hB

theorem normalizedG0Vec_first_return_sigma_nonlast_mid {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a b : ZMod m}
    (hab : a + b ≠ 0) (hs : a + b = (h : ZMod m)) (hB : b + 1 ≠ 0) :
    ((normalizedG0Vec (m := m))^[returnTimeSigma hm hh2 ⟨(a, b), hab⟩])
        (sigmaVec a b) =
      sigmaVec
        (nextSigma hm hh2 ⟨(a, b), hab⟩).1.1
        (nextSigma hm hh2 ⟨(a, b), hab⟩).1.2 := by
  rw [returnTimeSigma_nonlast_mid hm hh2 hab hs hB]
  rw [nextSigma_nonlast_mid hm hh2 hab hs hB]
  simp
  rw [Nat.mul_comm (2 * (h + 1)) m]
  rw [Function.iterate_mul]
  exact normalizedG0Vec_first_return_mid (m := m) (h := h) hm hh2
    (a := a) (b := b) hs hB

theorem normalizedG0Vec_first_return_sigma_nonlast_high {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a b : ZMod m} {s : Nat}
    (hab : a + b ≠ 0) (hspos : 0 < s) (hhs : h < s) (hsm : s < m)
    (hs : a + b = (s : ZMod m)) (hB : b + 1 ≠ 0) :
    ((normalizedG0Vec (m := m))^[returnTimeSigma hm hh2 ⟨(a, b), hab⟩])
        (sigmaVec a b) =
      sigmaVec
        (nextSigma hm hh2 ⟨(a, b), hab⟩).1.1
        (nextSigma hm hh2 ⟨(a, b), hab⟩).1.2 := by
  rw [returnTimeSigma_nonlast_high hm hh2 hab hhs hsm hs hB]
  rw [nextSigma_nonlast_high hm hh2 hab hhs hsm hs hB]
  simp
  rw [Nat.mul_comm (3 * h + 2) m]
  rw [Function.iterate_mul]
  exact normalizedG0Vec_first_return_high (m := m) (h := h) hm
    (a := a) (b := b) (s := s) hh2 hspos hhs hsm hs hB

theorem normalizedG0Vec_first_return_sigma_nonlast {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a b : ZMod m}
    (hab : a + b ≠ 0) (hB : b + 1 ≠ 0) :
    ((normalizedG0Vec (m := m))^[returnTimeSigma hm hh2 ⟨(a, b), hab⟩])
        (sigmaVec a b) =
      sigmaVec
        (nextSigma hm hh2 ⟨(a, b), hab⟩).1.1
        (nextSigma hm hh2 ⟨(a, b), hab⟩).1.2 := by
  let s := (a + b).val
  have hsm : s < m := ZMod.val_lt (a + b)
  have hs : a + b = (s : ZMod m) := by
    dsimp [s]
    exact (ZMod.natCast_zmod_val (a + b)).symm
  have hspos : 0 < s := by
    by_contra hnot
    have hs0 : s = 0 := by omega
    apply hab
    rw [hs, hs0]
    simp
  by_cases hsh : s < h
  · exact normalizedG0Vec_first_return_sigma_nonlast_low
      (m := m) (h := h) hm hh2 (a := a) (b := b) (s := s)
      hab hspos hsh hs hB
  · by_cases hseq : s = h
    · have hmid : a + b = (h : ZMod m) := by
        simpa [hseq] using hs
      exact normalizedG0Vec_first_return_sigma_nonlast_mid
        (m := m) (h := h) hm hh2 (a := a) (b := b) hab hmid hB
    · have hhs : h < s := by omega
      exact normalizedG0Vec_first_return_sigma_nonlast_high
        (m := m) (h := h) hm hh2 (a := a) (b := b) (s := s)
        hab hspos hhs hsm hs hB

theorem normalizedG0Vec_first_return_sigma_nonlast_low_p5_no_earlier
    {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a b : ZMod m} {s : Nat}
    (hab : a + b ≠ 0) (hspos : 0 < s) (hsh : s < h)
    (hs : a + b = (s : ZMod m)) (hB : b + 1 ≠ 0) :
    forall k : Nat, 0 < k -> k < returnTimeSigma hm hh2 ⟨(a, b), hab⟩ ->
      p5 (((normalizedG0Vec (m := m))^[k]) (sigmaVec a b)) ≠ 2 := by
  intro k hkpos hklt
  have hklt' : k < (h + 1) * m := by
    rw [returnTimeSigma_nonlast_low hm hh2 hab hspos hsh hs hB] at hklt
    exact hklt
  exact normalizedG0Vec_first_return_low_p5_no_earlier
    (m := m) (h := h) hm (a := a) (b := b) (s := s) hspos hsh hs hB
    k hkpos hklt'

theorem normalizedG0Vec_first_return_sigma_nonlast_mid_p5_no_earlier
    {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a b : ZMod m}
    (hab : a + b ≠ 0) (hs : a + b = (h : ZMod m)) (hB : b + 1 ≠ 0) :
    forall k : Nat, 0 < k -> k < returnTimeSigma hm hh2 ⟨(a, b), hab⟩ ->
      p5 (((normalizedG0Vec (m := m))^[k]) (sigmaVec a b)) ≠ 2 := by
  intro k hkpos hklt
  have hklt' : k < 2 * (h + 1) * m := by
    rw [returnTimeSigma_nonlast_mid hm hh2 hab hs hB] at hklt
    exact hklt
  exact normalizedG0Vec_first_return_mid_p5_no_earlier
    (m := m) (h := h) hm hh2 (a := a) (b := b) hs hB k hkpos hklt'

theorem normalizedG0Vec_first_return_sigma_nonlast_high_p5_no_earlier
    {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a b : ZMod m} {s : Nat}
    (hab : a + b ≠ 0) (hspos : 0 < s) (hhs : h < s) (hsm : s < m)
    (hs : a + b = (s : ZMod m)) (hB : b + 1 ≠ 0) :
    forall k : Nat, 0 < k -> k < returnTimeSigma hm hh2 ⟨(a, b), hab⟩ ->
      p5 (((normalizedG0Vec (m := m))^[k]) (sigmaVec a b)) ≠ 2 := by
  intro k hkpos hklt
  have hklt' : k < (3 * h + 2) * m := by
    rw [returnTimeSigma_nonlast_high hm hh2 hab hhs hsm hs hB] at hklt
    exact hklt
  exact normalizedG0Vec_first_return_high_p5_no_earlier
    (m := m) (h := h) hm (a := a) (b := b) (s := s)
    hh2 hspos hhs hsm hs hB k hkpos hklt'

theorem normalizedG0Vec_first_return_sigma_nonlast_p5_no_earlier
    {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a b : ZMod m}
    (hab : a + b ≠ 0) (hB : b + 1 ≠ 0) :
    forall k : Nat, 0 < k -> k < returnTimeSigma hm hh2 ⟨(a, b), hab⟩ ->
      p5 (((normalizedG0Vec (m := m))^[k]) (sigmaVec a b)) ≠ 2 := by
  let s := (a + b).val
  have hsm : s < m := ZMod.val_lt (a + b)
  have hs : a + b = (s : ZMod m) := by
    dsimp [s]
    exact (ZMod.natCast_zmod_val (a + b)).symm
  have hspos : 0 < s := by
    by_contra hnot
    have hs0 : s = 0 := by omega
    apply hab
    rw [hs, hs0]
    simp
  by_cases hsh : s < h
  · exact normalizedG0Vec_first_return_sigma_nonlast_low_p5_no_earlier
      (m := m) (h := h) hm hh2 (a := a) (b := b) (s := s)
      hab hspos hsh hs hB
  · by_cases hseq : s = h
    · have hmid : a + b = (h : ZMod m) := by
        simpa [hseq] using hs
      exact normalizedG0Vec_first_return_sigma_nonlast_mid_p5_no_earlier
        (m := m) (h := h) hm hh2 (a := a) (b := b) hab hmid hB
    · have hhs : h < s := by omega
      exact normalizedG0Vec_first_return_sigma_nonlast_high_p5_no_earlier
        (m := m) (h := h) hm hh2 (a := a) (b := b) (s := s)
        hab hspos hhs hsm hs hB

theorem zmod_nat_sub_one_ne_zero_of_two_le {m r : Nat} [NeZero m]
    (hr2 : 2 <= r) (hrm : r < m) :
    ((r : ZMod m) - 1) ≠ 0 := by
  have hne : (((r - 1 : Nat) : ZMod m)) ≠ 0 := by
    apply zmod_nat_ne_zero (m := m) (k := r - 1) <;> omega
  intro h
  apply hne
  rw [zmod_nat_pred_eq_sub_one (m := m) (s := r) (by omega)]
  exact h

theorem normalizedG0Vec_last_short_phase1 {m r j : Nat} [NeZero m]
    (hr2 : 2 <= r) (hrm : r < m) (hj : j <= r - 2) :
    ((normalizedG0Vec (m := m))^[1 + j])
      (sigmaVec ((r : Nat) : ZMod m) (-1)) =
    ![
      (-3 : ZMod m) - (2 : ZMod m) * (j : ZMod m),
      (r : ZMod m),
      0,
      1 + (j : ZMod m),
      2 - (r : ZMod m) + (j : ZMod m)
    ] := by
  let G := normalizedG0Vec (m := m)
  let w0 : Vec5 m := sigmaVec ((r : Nat) : ZMod m) (-1)
  let w1 : Vec5 m := ![-3, (r : ZMod m), 0, 1, 2 - (r : ZMod m)]
  have hr0 : ((r : Nat) : ZMod m) ≠ 0 := by
    apply zmod_nat_ne_zero (m := m) (k := r) <;> omega
  have hab : ((r : ZMod m) + (-1 : ZMod m)) ≠ 0 := by
    simpa [sub_eq_add_neg] using
      (zmod_nat_sub_one_ne_zero_of_two_le (m := m) (r := r) hr2 hrm)
  have hGw0 : G w0 = w1 := by
    dsimp [G, w0, w1]
    rw [normalizedG0Vec_sigmaVec hab]
    ext i
    fin_cases i <;> simp
    all_goals ring
  have hw1run : G^[j] w1 = w1 + j • normalizedG0Delta0 m := by
    dsimp [G]
    apply normalizedG0Vec_iter_eq_add_delta0_of_coords134
    · dsimp [w1]
      exact hr0
    · intro k hk
      dsimp [w1]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := k) (by omega)
    · intro k hk
      dsimp [w1]
      exact zmod_two_sub_nat_add_nat_ne_zero (m := m) (s := r) (k := k) (by omega) hrm
  have hiter : G^[1 + j] w0 = G^[j] (G w0) := by
    have h_eq : 1 + j = j + 1 := by omega
    simpa [h_eq] using (Function.iterate_succ_apply' G j w0)
  change G^[1 + j] w0 =
    ![
      (-3 : ZMod m) - (2 : ZMod m) * (j : ZMod m),
      (r : ZMod m),
      0,
      1 + (j : ZMod m),
      2 - (r : ZMod m) + (j : ZMod m)
    ]
  rw [hiter, hGw0, hw1run]
  dsimp [w1]
  ext i
  fin_cases i <;> simp [normalizedG0Delta0]
  all_goals ring

theorem zmod_one_add_nat_sub_two_ne_zero {m r : Nat} [NeZero m]
    (hr2 : 2 <= r) (hrm : r < m) :
    ((1 : ZMod m) + ((r - 2 : Nat) : ZMod m)) ≠ 0 := by
  have hne : (((r - 1 : Nat) : ZMod m)) ≠ 0 := by
    apply zmod_nat_ne_zero (m := m) (k := r - 1) <;> omega
  have hcast : (((r - 1 : Nat) : ZMod m)) =
      (1 : ZMod m) + ((r - 2 : Nat) : ZMod m) := by
    have hr_eq : r - 1 = 1 + (r - 2) := by omega
    rw [hr_eq]
    simp [Nat.cast_add]
  intro h
  exact hne (by rw [hcast, h])

theorem normalizedG0Vec_last_short_phase2 {m r j : Nat} [NeZero m]
    (hm5 : 5 <= m) (hr2 : 2 <= r) (hrm : r < m)
    (hj : j <= m - r - 1) :
    ((normalizedG0Vec (m := m))^[r + j])
      (sigmaVec ((r : Nat) : ZMod m) (-1)) =
    ![
      (-2 : ZMod m) * (r : ZMod m) - 2 - (2 : ZMod m) * (j : ZMod m),
      (r : ZMod m),
      0,
      (r : ZMod m) + 1 + (j : ZMod m),
      1 + (j : ZMod m)
    ] := by
  let G := normalizedG0Vec (m := m)
  let w0 : Vec5 m := sigmaVec ((r : Nat) : ZMod m) (-1)
  let wSwitch : Vec5 m :=
    ![
      (-3 : ZMod m) - (2 : ZMod m) * ((r - 2 : Nat) : ZMod m),
      (r : ZMod m),
      0,
      1 + ((r - 2 : Nat) : ZMod m),
      2 - (r : ZMod m) + ((r - 2 : Nat) : ZMod m)
    ]
  let w2 : Vec5 m :=
    ![
      (-2 : ZMod m) * (r : ZMod m) - 2,
      (r : ZMod m),
      0,
      (r : ZMod m) + 1,
      1
    ]
  have hr0 : ((r : Nat) : ZMod m) ≠ 0 := by
    apply zmod_nat_ne_zero (m := m) (k := r) <;> omega
  have hphase1' : G^[r - 2] (G w0) = wSwitch := by
    have hiter1 : G^[1 + (r - 2)] w0 = G^[r - 2] (G w0) := by
      have h_eq : 1 + (r - 2) = (r - 2) + 1 := by omega
      simpa [h_eq] using (Function.iterate_succ_apply' G (r - 2) w0)
    rw [← hiter1]
    change ((normalizedG0Vec (m := m))^[1 + (r - 2)])
        (sigmaVec ((r : Nat) : ZMod m) (-1)) = wSwitch
    exact normalizedG0Vec_last_short_phase1 (m := m) (r := r) (j := r - 2)
      hr2 hrm (by omega)
  have hp3 : p5 wSwitch = 3 := by
    apply p5_eq_three_of_one_three_ne_zero_two_four_zero
    · dsimp [wSwitch]
      exact hr0
    · dsimp [wSwitch]
      exact zmod_one_add_nat_sub_two_ne_zero (m := m) (r := r) hr2 hrm
    · dsimp [wSwitch]
    · dsimp [wSwitch]
      rw [zmod_nat_sub_two_eq_sub_two (m := m) (s := r) hr2]
      ring
  have hAfter3 : G wSwitch = w2 := by
    dsimp [G]
    rw [normalizedG0Vec_eq_of_p5_eq_three hp3]
    dsimp [wSwitch, w2]
    ext i
    fin_cases i <;> simp [normalizedG0Delta3]
    all_goals
      rw [zmod_nat_sub_two_eq_sub_two (m := m) (s := r) hr2]
      ring
  have hw2run : G^[j] w2 = w2 + j • normalizedG0Delta0 m := by
    dsimp [G]
    apply normalizedG0Vec_iter_eq_add_delta0_of_coords134
    · dsimp [w2]
      exact hr0
    · intro k hk
      dsimp [w2]
      exact zmod_nat_add_one_add_nat_ne_zero (m := m) (s := r) (k := k)
        (by omega) hrm
    · intro k hk
      dsimp [w2]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := k) (by omega)
  have hiter : G^[r + j] w0 = G^[j] (G (G^[r - 2] (G w0))) := by
    have hdecomp : r + j = j + (1 + ((r - 2) + 1)) := by omega
    simpa [hdecomp] using (iterate_decomp4 G w0 (r - 2) j)
  change G^[r + j] w0 =
    ![
      (-2 : ZMod m) * (r : ZMod m) - 2 - (2 : ZMod m) * (j : ZMod m),
      (r : ZMod m),
      0,
      (r : ZMod m) + 1 + (j : ZMod m),
      1 + (j : ZMod m)
    ]
  rw [hiter, hphase1', hAfter3, hw2run]
  dsimp [w2]
  ext i
  fin_cases i <;> simp [normalizedG0Delta0]
  all_goals ring

theorem normalizedG0Vec_first_return_last_nonzero_rep {m h r : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h)
    (hr2 : 2 <= r) (hrm : r < m) :
    ((normalizedG0Vec (m := m))^[m - 1])
      (sigmaVec ((r : Nat) : ZMod m) (-1)) =
    sigmaVec ((r : Nat) : ZMod m) 0 := by
  have hm5 : 5 <= m := by omega
  have hphase := normalizedG0Vec_last_short_phase2 (m := m) (r := r)
    (j := m - r - 1) hm5 hr2 hrm (by omega)
  have htime : m - 1 = r + (m - r - 1) := by omega
  rw [htime]
  rw [hphase]
  ext i
  fin_cases i <;> simp [sigmaVec]
  · have hzero := zmod_nat_add_one_add_complement (m := m) (s := r) hrm
    have hcomp : (((m - r - 1 : Nat) : ZMod m)) = -(r : ZMod m) - 1 := by
      linear_combination hzero
    rw [hcomp]
    ring
  · have hzero := zmod_nat_add_one_add_complement (m := m) (s := r) hrm
    simpa [add_assoc, add_comm, add_left_comm] using hzero
  · have hneg := zmod_one_add_complement_eq_neg (m := m) (s := r) hrm
    simpa [add_assoc, add_comm, add_left_comm] using hneg

theorem normalizedG0Vec_first_return_last_nonzero {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a : ZMod m}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    ((normalizedG0Vec (m := m))^[m - 1]) (sigmaVec a (-1)) =
      sigmaVec a 0 := by
  let r := a.val
  have hrm : r < m := ZMod.val_lt a
  have ha_repr : ((r : Nat) : ZMod m) = a := by
    dsimp [r]
    exact ZMod.natCast_zmod_val a
  have hr0 : r ≠ 0 := by
    intro h
    apply ha0
    rw [← ha_repr, h]
    simp
  have hr1 : r ≠ 1 := by
    intro h
    apply ha1
    rw [← ha_repr, h]
    simp
  have hr2 : 2 <= r := by omega
  simpa [ha_repr] using
    normalizedG0Vec_first_return_last_nonzero_rep
      (m := m) (h := h) (r := r) hm hh2 hr2 hrm

theorem normalizedG0Vec_last_nonzero_p5_no_earlier {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a : ZMod m}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    forall k : Nat, 0 < k -> k < m - 1 ->
      p5 (((normalizedG0Vec (m := m))^[k]) (sigmaVec a (-1))) ≠ 2 := by
  intro k hkpos hklt
  let r := a.val
  have hrm : r < m := ZMod.val_lt a
  have ha_repr : ((r : Nat) : ZMod m) = a := by
    dsimp [r]
    exact ZMod.natCast_zmod_val a
  have hr0 : r ≠ 0 := by
    intro h0
    apply ha0
    rw [← ha_repr, h0]
    simp
  have hr1 : r ≠ 1 := by
    intro h1
    apply ha1
    rw [← ha_repr, h1]
    simp
  have hr2 : 2 <= r := by omega
  by_cases hkr : k < r
  · let j := k - 1
    have hj : j <= r - 2 := by
      dsimp [j]
      omega
    have hk_eq : k = 1 + j := by
      dsimp [j]
      omega
    have hstate :
        ((normalizedG0Vec (m := m))^[k]) (sigmaVec a (-1)) =
        ![
          (-3 : ZMod m) - (2 : ZMod m) * (j : ZMod m),
          (r : ZMod m),
          0,
          1 + (j : ZMod m),
          2 - (r : ZMod m) + (j : ZMod m)
        ] := by
      rw [← ha_repr, hk_eq]
      exact normalizedG0Vec_last_short_phase1
        (m := m) (r := r) (j := j) hr2 hrm hj
    have hwroot :
        Root5 m (((normalizedG0Vec (m := m))^[k]) (sigmaVec a (-1))) := by
      rw [hstate]
      unfold Root5 sum5
      rw [Fin.sum_univ_five]
      simp
      ring
    have h3ne :
        (((normalizedG0Vec (m := m))^[k]) (sigmaVec a (-1))) 3 ≠ 0 := by
      rw [hstate]
      simp
      exact zmod_one_add_nat_ne_zero_before_mod
        (m := m) (k := j) (by dsimp [j]; omega)
    exact p5_ne_two_of_root_guard hwroot (Or.inr (Or.inl h3ne))
  · let j := k - r
    have hj_le : j <= m - r - 1 := by
      dsimp [j]
      omega
    have hj_lt : j < m - r - 1 := by
      dsimp [j]
      omega
    have hk_eq : k = r + j := by
      dsimp [j]
      omega
    have hm5 : 5 <= m := by omega
    have hstate :
        ((normalizedG0Vec (m := m))^[k]) (sigmaVec a (-1)) =
        ![
          (-2 : ZMod m) * (r : ZMod m) - 2 - (2 : ZMod m) * (j : ZMod m),
          (r : ZMod m),
          0,
          (r : ZMod m) + 1 + (j : ZMod m),
          1 + (j : ZMod m)
        ] := by
      rw [← ha_repr, hk_eq]
      exact normalizedG0Vec_last_short_phase2
        (m := m) (r := r) (j := j) hm5 hr2 hrm hj_le
    have hwroot :
        Root5 m (((normalizedG0Vec (m := m))^[k]) (sigmaVec a (-1))) := by
      rw [hstate]
      unfold Root5 sum5
      rw [Fin.sum_univ_five]
      simp
      ring
    have h3ne :
        (((normalizedG0Vec (m := m))^[k]) (sigmaVec a (-1))) 3 ≠ 0 := by
      rw [hstate]
      simp
      exact zmod_nat_add_one_add_nat_ne_zero
        (m := m) (s := r) (k := j) hj_lt hrm
    exact p5_ne_two_of_root_guard hwroot (Or.inr (Or.inl h3ne))

theorem returnTimeSigma_last_nonzero {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a : ZMod m}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    returnTimeSigma hm hh2 (lastSigmaParam a ha1) = m - 1 := by
  simp [returnTimeSigma, lastSigmaParam, ha0]

theorem nextSigma_last_nonzero {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a : ZMod m}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    nextSigma hm hh2 (lastSigmaParam a ha1) =
      ⟨(a, 0), by simpa using ha0⟩ := by
  apply Subtype.ext
  simp [nextSigma, lastSigmaParam, ha0]

theorem normalizedG0Vec_first_return_sigma_last_nonzero {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a : ZMod m}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    ((normalizedG0Vec (m := m))^[returnTimeSigma hm hh2 (lastSigmaParam a ha1)])
        (sigmaVec a (-1)) =
      sigmaVec
        (nextSigma hm hh2 (lastSigmaParam a ha1)).1.1
        (nextSigma hm hh2 (lastSigmaParam a ha1)).1.2 := by
  rw [returnTimeSigma_last_nonzero hm hh2 ha0 ha1]
  rw [nextSigma_last_nonzero hm hh2 ha0 ha1]
  exact normalizedG0Vec_first_return_last_nonzero hm hh2 ha0 ha1

theorem normalizedG0Vec_last_zero_initial_phase1 {m h j : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (hj : j <= m - 1) :
    ((normalizedG0Vec (m := m))^[1 + j]) (sigmaVec 0 (-1)) =
    ![
      (-3 : ZMod m) - (3 : ZMod m) * (j : ZMod m),
      0,
      0,
      1 + (j : ZMod m),
      2 + (j : ZMod m) * (2 : ZMod m)
    ] := by
  let G := normalizedG0Vec (m := m)
  let w0 : Vec5 m := sigmaVec 0 (-1)
  let w1 : Vec5 m := ![-3, 0, 0, 1, (2 : ZMod m)]
  have hab : (0 : ZMod m) + (-1 : ZMod m) ≠ 0 := by
    simpa using (zmod_neg_nat_ne_zero (m := m) (n := 1) (by omega) (by omega))
  have hGw0 : G w0 = w1 := by
    dsimp [G, w0, w1]
    rw [normalizedG0Vec_sigmaVec hab]
    ext i
    fin_cases i <;> simp
    all_goals ring
  have hw1run : G^[j] w1 = w1 + j • normalizedG0Delta4 m := by
    dsimp [G]
    apply normalizedG0Vec_iter_eq_add_delta4_of_coords12_3_04
    · dsimp [w1]
    · dsimp [w1]
    · intro k hk
      dsimp [w1]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := k) (by omega)
    · intro k hk
      dsimp [w1]
      right
      have hne := zmod_odd_two_mul_nat_ne_zero (m := m) (h := h) (n := k + 1)
        hm (by omega) (by omega)
      intro hz
      apply hne
      have heq : (((2 * (k + 1) : Nat) : ZMod m)) =
          (2 : ZMod m) + (k : ZMod m) * (2 : ZMod m) := by
        simp [Nat.cast_mul, Nat.cast_add]
        ring
      rwa [heq]
  have hiter : G^[1 + j] w0 = G^[j] (G w0) := by
    have h_eq : 1 + j = j + 1 := by omega
    simpa [h_eq] using (Function.iterate_succ_apply' G j w0)
  change G^[1 + j] w0 =
    ![
      (-3 : ZMod m) - (3 : ZMod m) * (j : ZMod m),
      0,
      0,
      1 + (j : ZMod m),
      2 + (j : ZMod m) * (2 : ZMod m)
    ]
  rw [hiter, hGw0, hw1run]
  dsimp [w1]
  ext i
  fin_cases i <;> simp [normalizedG0Delta4]
  all_goals ring

theorem zmod_last_zero_phase2_guard {m h k : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (hk : k < m - 1) :
    ((-2 : ZMod m) + (k : ZMod m) * (-3 : ZMod m) ≠ 0) ∨
      ((1 : ZMod m) + (k : ZMod m) * (2 : ZMod m) ≠ 0) := by
  by_cases hright : (1 : ZMod m) + (k : ZMod m) * (2 : ZMod m) ≠ 0
  · exact Or.inr hright
  · left
    have hright0 : (1 : ZMod m) + (k : ZMod m) * (2 : ZMod m) = 0 :=
      not_not.mp hright
    have hcast : (((2 * k + 1 : Nat) : ZMod m)) = 0 := by
      have heq : (((2 * k + 1 : Nat) : ZMod m)) =
          (1 : ZMod m) + (k : ZMod m) * (2 : ZMod m) := by
        simp [Nat.cast_mul, Nat.cast_add]
        ring
      rw [heq, hright0]
    have hd : m ∣ 2 * k + 1 := (ZMod.natCast_eq_zero_iff (2 * k + 1) m).mp hcast
    rcases hd with ⟨q, hq⟩
    have hq2 : q < 2 := by
      apply Nat.lt_of_mul_lt_mul_right (a := m)
      calc
        q * m = m * q := by rw [mul_comm]
        _ = 2 * k + 1 := hq.symm
        _ < 2 * m := by omega
    have hk_eq : k = h := by
      interval_cases q <;> omega
    have hne : (-(((h + 1 : Nat) : ZMod m))) ≠ 0 := by
      apply zmod_neg_nat_ne_zero (m := m) (n := h + 1) <;> omega
    intro hleft0
    apply hne
    have hmzero : ((2 * h + 1 : Nat) : ZMod m) = 0 := by
      rw [← hm]
      exact ZMod.natCast_self m
    have hmzero' : (2 : ZMod m) * (h : ZMod m) + 1 = 0 := by
      simpa [Nat.cast_mul, Nat.cast_add] using hmzero
    have hleft_h : (-2 : ZMod m) + (h : ZMod m) * (-3 : ZMod m) = 0 := by
      simpa [hk_eq] using hleft0
    rw [Nat.cast_add]
    ring_nf
    linear_combination hleft_h + hmzero'

theorem normalizedG0Vec_last_zero_initial_phase2 {m h j : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (hj : j <= m - 1) :
    ((normalizedG0Vec (m := m))^[m + 1 + j]) (sigmaVec 0 (-1)) =
    ![
      (-2 : ZMod m) - (3 : ZMod m) * (j : ZMod m),
      0,
      0,
      1 + (j : ZMod m),
      1 + (j : ZMod m) * (2 : ZMod m)
    ] := by
  let G := normalizedG0Vec (m := m)
  let w0 : Vec5 m := sigmaVec 0 (-1)
  let wZero : Vec5 m := ![0, 0, 0, 0, (0 : ZMod m)]
  let w2 : Vec5 m := ![-2, 0, 0, 1, (1 : ZMod m)]
  have hphase1' : G^[m - 1] (G w0) = wZero := by
    have hiter1 : G^[1 + (m - 1)] w0 = G^[m - 1] (G w0) := by
      have h_eq : 1 + (m - 1) = (m - 1) + 1 := by omega
      simpa [h_eq] using (Function.iterate_succ_apply' G (m - 1) w0)
    rw [← hiter1]
    change ((normalizedG0Vec (m := m))^[1 + (m - 1)])
        (sigmaVec 0 (-1)) = wZero
    rw [normalizedG0Vec_last_zero_initial_phase1 (m := m) (h := h)
      (j := m - 1) hm hh2 (by omega)]
    ext i
    fin_cases i <;> simp [wZero]
    · rw [zmod_nat_pred_self_eq_neg_one (m := m)]
      ring
    · exact zmod_one_add_nat_pred_self (m := m)
    · rw [zmod_nat_pred_self_eq_neg_one (m := m)]
      ring
  have hAfter0 : G wZero = w2 := by
    have hp : p5 wZero = 0 := by
      dsimp [wZero]
      rw [p5]
      rw [zeroMaskMinusOne_eq_mask5]
      simp [Lambda1, mask5, row5]
    dsimp [G]
    rw [normalizedG0Vec_eq_of_p5_eq_zero hp]
    dsimp [wZero, w2]
    ext i
    fin_cases i <;> simp [normalizedG0Delta0]
  have hw2run : G^[j] w2 = w2 + j • normalizedG0Delta4 m := by
    dsimp [G]
    apply normalizedG0Vec_iter_eq_add_delta4_of_coords12_3_04
    · dsimp [w2]
    · dsimp [w2]
    · intro k hk
      dsimp [w2]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := k) (by omega)
    · intro k hk
      dsimp [w2]
      exact zmod_last_zero_phase2_guard (m := m) (h := h) (k := k) hm hh2 (by omega)
  have hiter : G^[m + 1 + j] w0 = G^[j] (G (G^[m - 1] (G w0))) := by
    have hdecomp : m + 1 + j = j + (1 + ((m - 1) + 1)) := by omega
    simpa [hdecomp] using (iterate_decomp4 G w0 (m - 1) j)
  change G^[m + 1 + j] w0 =
    ![
      (-2 : ZMod m) - (3 : ZMod m) * (j : ZMod m),
      0,
      0,
      1 + (j : ZMod m),
      1 + (j : ZMod m) * (2 : ZMod m)
    ]
  rw [hiter, hphase1', hAfter0, hw2run]
  dsimp [w2]
  ext i
  fin_cases i <;> simp [normalizedG0Delta4]
  all_goals ring

theorem normalizedG0Vec_last_zero_initial {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    ((normalizedG0Vec (m := m))^[2 * m]) (sigmaVec 0 (-1)) =
      EVec 1 0 := by
  have hphase := normalizedG0Vec_last_zero_initial_phase2 (m := m) (h := h)
    (j := m - 1) hm hh2 (by omega)
  have htime : 2 * m = m + 1 + (m - 1) := by omega
  rw [htime]
  rw [hphase]
  ext i
  fin_cases i <;> simp [EVec]
  · rw [zmod_nat_pred_self_eq_neg_one (m := m)]
    ring
  · exact zmod_one_add_nat_pred_self (m := m)
  · rw [zmod_nat_pred_self_eq_neg_one (m := m)]
    ring

theorem zmod_E_quick_delta4_guard {m k : Nat} [NeZero m] {u : ZMod m}
    (hk : k < m - 1) :
    (u - 3 + (k : ZMod m) * (-3 : ZMod m) ≠ 0) ∨
      ((2 : ZMod m) - u + (k : ZMod m) * 2 ≠ 0) := by
  by_cases h4 : (2 : ZMod m) - u + (k : ZMod m) * 2 ≠ 0
  · exact Or.inr h4
  · left
    intro h0
    have h4zero : (2 : ZMod m) - u + (k : ZMod m) * 2 = 0 := not_not.mp h4
    have hsum : (1 : ZMod m) + (k : ZMod m) = 0 := by
      linear_combination -(h0 + h4zero)
    exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := k) hk hsum

theorem normalizedG0Vec_E_quick {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h)
    {u : ZMod m} (hu : u ≠ 0) (hu1 : u ≠ 1) :
    ((normalizedG0Vec (m := m))^[m]) (EVec u (-1)) =
      EVec u 0 := by
  let G := normalizedG0Vec (m := m)
  let w0 : Vec5 m := EVec u (-1)
  let w1 : Vec5 m := ![u - 3, 0, 0, 1, (2 : ZMod m) - u]
  have hs : u + (-1 : ZMod m) ≠ 0 := by
    intro h
    apply hu1
    linear_combination h
  have hGw0 : G w0 = w1 := by
    dsimp [G, w0, w1]
    rw [normalizedG0Vec_eq_of_p5_eq_one (p5_EVec_eq_one hu hs)]
    ext i
    fin_cases i <;> simp [EVec, normalizedG0Delta1]
    all_goals ring
  let n := m - 1
  have hw1run : G^[n] w1 = w1 + n • normalizedG0Delta4 m := by
    dsimp [G]
    apply normalizedG0Vec_iter_eq_add_delta4_of_coords12_3_04
    · dsimp [w1]
    · dsimp [w1]
    · intro k hk
      dsimp [w1]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := k) (by simpa [n] using hk)
    · intro k hk
      dsimp [w1]
      exact zmod_E_quick_delta4_guard (m := m) (k := k) (u := u) (by simpa [n] using hk)
  have hdecomp : m = n + 1 := by
    have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    omega
  have hiter : G^[m] w0 = G^[n] (G w0) := by
    simpa [hdecomp] using (Function.iterate_succ_apply' G n w0)
  change G^[m] w0 = EVec u 0
  rw [hiter, hGw0, hw1run]
  dsimp [w1, n]
  ext i
  fin_cases i <;> simp [EVec, normalizedG0Delta4]
  · rw [zmod_nat_pred_self_eq_neg_one (m := m)]
    ring
  · exact zmod_one_add_nat_pred_self (m := m)
  · rw [zmod_nat_pred_self_eq_neg_one (m := m)]
    ring

theorem normalizedG0Vec_E_quick_p5_no_earlier {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h)
    {u : ZMod m} (hu : u ≠ 0) (hu1 : u ≠ 1) :
    forall k : Nat, 0 < k -> k < m ->
      p5 (((normalizedG0Vec (m := m))^[k]) (EVec u (-1))) ≠ 2 := by
  intro k hkpos hklt
  let j := k - 1
  let w1 : Vec5 m := ![u - 3, 0, 0, 1, (2 : ZMod m) - u]
  have hs : u + (-1 : ZMod m) ≠ 0 := by
    intro h
    apply hu1
    linear_combination h
  have hGw0 : normalizedG0Vec (m := m) (EVec u (-1)) = w1 := by
    dsimp [w1]
    rw [normalizedG0Vec_eq_of_p5_eq_one (p5_EVec_eq_one hu hs)]
    ext i
    fin_cases i <;> simp [EVec, normalizedG0Delta1]
    all_goals ring
  have hjlt : j < m - 1 := by
    dsimp [j]
    omega
  have hk_eq : k = 1 + j := by
    dsimp [j]
    omega
  have hstate :
      ((normalizedG0Vec (m := m))^[k]) (EVec u (-1)) =
        w1 + j • normalizedG0Delta4 m := by
    have hiter : ((normalizedG0Vec (m := m))^[k]) (EVec u (-1)) =
        ((normalizedG0Vec (m := m))^[j])
          (normalizedG0Vec (m := m) (EVec u (-1))) := by
      rw [hk_eq]
      have h_eq : 1 + j = j + 1 := by omega
      simpa [h_eq] using
        (Function.iterate_succ_apply' (normalizedG0Vec (m := m)) j (EVec u (-1)))
    rw [hiter, hGw0]
    apply normalizedG0Vec_iter_eq_add_delta4_of_coords12_3_04
    · dsimp [w1]
    · dsimp [w1]
    · intro r hr
      dsimp [w1]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := r) (by omega)
    · intro r hr
      dsimp [w1]
      exact zmod_E_quick_delta4_guard (m := m) (k := r) (u := u) (by omega)
  have h3ne : (((normalizedG0Vec (m := m))^[k]) (EVec u (-1))) 3 ≠ 0 := by
    rw [hstate]
    dsimp [w1]
    simp [normalizedG0Delta4]
    exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := j) hjlt
  exact p5_ne_two_of_three_ne_zero h3ne

theorem normalizedG0Vec_E_generic {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h)
    {u v : ZMod m}
    (hu : u ≠ 0) (hs : u + v ≠ 0)
    (hV0 : v + 1 ≠ 0) (hVu : v + 1 ≠ -u) :
    ((normalizedG0Vec (m := m))^[m - 1]) (EVec u v) =
      EVec u (v + 1) := by
  let G := normalizedG0Vec (m := m)
  let s := (u + v).val
  let w0 : Vec5 m := EVec u v
  let w1 : Vec5 m := ![u - 3, v + 1, 0, 1, (1 : ZMod m) - (s : ZMod m)]
  have hs_repr : ((s : Nat) : ZMod m) = u + v := by
    dsimp [s]
    exact ZMod.natCast_zmod_val (u + v)
  have hspos : 0 < s := by
    have hs0 : s ≠ 0 := by
      intro h
      apply hs
      rw [← hs_repr, h]
      simp
    omega
  have hsm : s < m := ZMod.val_lt (u + v)
  have hslt : s < m - 1 := by
    have hlast : s ≠ m - 1 := by
      intro hlast
      apply hVu
      have hsum : u + v + 1 = 0 := by
        rw [← hs_repr, hlast]
        rw [zmod_nat_pred_self_eq_neg_one (m := m)]
        ring
      linear_combination hsum
    omega
  have hGw0 : G w0 = w1 := by
    dsimp [G, w0, w1]
    rw [normalizedG0Vec_eq_of_p5_eq_one (p5_EVec_eq_one hu hs)]
    ext i
    fin_cases i <;> simp [EVec, normalizedG0Delta1]
    · ring
    · rw [hs_repr]
      ring
  let n1 := s - 1
  let n2 := m - s - 2
  have hw1run : G^[n1] w1 = w1 + n1 • normalizedG0Delta0 m := by
    dsimp [G]
    apply normalizedG0Vec_iter_eq_add_delta0_of_coords134
    · dsimp [w1]
      exact hV0
    · intro k hk
      dsimp [w1]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := k) (by omega)
    · intro k hk
      dsimp [w1]
      exact zmod_one_sub_nat_add_nat_ne_zero (m := m) (s := s) (k := k)
        (by simpa [n1] using hk) hsm
  have hp3 : p5 (G^[n1] w1) = 3 := by
    rw [hw1run]
    apply p5_eq_three_of_one_three_ne_zero_two_four_zero
    · dsimp [w1, n1]
      simp [normalizedG0Delta0]
      simpa [normalizedG0Delta0] using hV0
    · dsimp [w1, n1]
      intro h
      have hsne : ((s : Nat) : ZMod m) ≠ 0 := by
        apply zmod_nat_ne_zero (m := m) (k := s) <;> omega
      apply hsne
      have h' : (1 : ZMod m) + (((s - 1 : Nat) : ZMod m)) = 0 := by
        simpa [normalizedG0Delta0] using h
      simpa [zmod_one_add_nat_pred m s hspos] using h'
    · dsimp [w1, n1]
      simp [normalizedG0Delta0]
    · dsimp [w1, n1]
      simp [normalizedG0Delta0]
      exact zmod_one_sub_add_nat_pred m s hspos
  let w2 : Vec5 m :=
    ![
      u - 3 + ((s - 1 : Nat) : ZMod m) * (-2 : ZMod m) - 3,
      v + 1,
      0,
      (s : ZMod m) + 2,
      1
    ]
  have hAfter3 : G (G^[n1] w1) = w2 := by
    have hp3' : p5 (w1 + n1 • normalizedG0Delta0 m) = 3 := by
      simpa [hw1run] using hp3
    rw [hw1run]
    dsimp [G]
    rw [normalizedG0Vec_eq_of_p5_eq_three hp3']
    dsimp [w1, w2, n1]
    ext i
    fin_cases i <;> simp [normalizedG0Delta0, normalizedG0Delta3]
    · rw [zmod_nat_pred_eq_sub_one (m := m) (s := s) hspos]
      ring
    · rw [zmod_nat_pred_eq_sub_one (m := m) (s := s) hspos]
      ring
    · rw [zmod_nat_pred_eq_sub_one (m := m) (s := s) hspos]
      ring
  have hw2run : G^[n2] w2 = w2 + n2 • normalizedG0Delta0 m := by
    dsimp [G]
    apply normalizedG0Vec_iter_eq_add_delta0_of_coords134
    · dsimp [w2]
      exact hV0
    · intro k hk
      dsimp [w2]
      exact zmod_nat_add_two_add_nat_ne_zero (m := m) (s := s) (k := k)
        (by simpa [n2] using hk)
    · intro k hk
      dsimp [w2]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := k) (by omega)
  have hdecomp : m - 1 = n2 + (1 + (n1 + 1)) := by omega
  have hiter : G^[m - 1] w0 = G^[n2] (G (G^[n1] (G w0))) := by
    simpa [hdecomp] using (iterate_decomp4 G w0 n1 n2)
  change G^[m - 1] w0 = EVec u (v + 1)
  rw [hiter, hGw0, hAfter3, hw2run]
  dsimp [w2, n1, n2]
  have hcomp := zmod_nat_add_two_add_complement (m := m) (s := s) hslt
  have hn2 : (((m - s - 2 : Nat) : ZMod m)) = -(s : ZMod m) - 2 := by
    linear_combination hcomp
  ext i
  fin_cases i <;> simp [EVec, normalizedG0Delta0]
  · rw [zmod_nat_pred_eq_sub_one (m := m) (s := s) hspos]
    rw [hn2]
    ring
  · rw [hcomp]
  · rw [hn2]
    rw [hs_repr]
    ring

theorem normalizedG0Vec_E_generic_p5_no_earlier {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h)
    {u v : ZMod m}
    (hu : u ≠ 0) (hs : u + v ≠ 0)
    (hV0 : v + 1 ≠ 0) (hVu : v + 1 ≠ -u) :
    forall k : Nat, 0 < k -> k < m - 1 ->
      p5 (((normalizedG0Vec (m := m))^[k]) (EVec u v)) ≠ 2 := by
  intro k hkpos hklt
  let G := normalizedG0Vec (m := m)
  let s := (u + v).val
  let w0 : Vec5 m := EVec u v
  let w1 : Vec5 m := ![u - 3, v + 1, 0, 1, (1 : ZMod m) - (s : ZMod m)]
  have hs_repr : ((s : Nat) : ZMod m) = u + v := by
    dsimp [s]
    exact ZMod.natCast_zmod_val (u + v)
  have hspos : 0 < s := by
    have hs0 : s ≠ 0 := by
      intro h
      apply hs
      rw [← hs_repr, h]
      simp
    omega
  have hsm : s < m := ZMod.val_lt (u + v)
  have hslt : s < m - 1 := by
    have hlast : s ≠ m - 1 := by
      intro hlast
      apply hVu
      have hsum : u + v + 1 = 0 := by
        rw [← hs_repr, hlast]
        rw [zmod_nat_pred_self_eq_neg_one (m := m)]
        ring
      linear_combination hsum
    omega
  have hGw0 : G w0 = w1 := by
    dsimp [G, w0, w1]
    rw [normalizedG0Vec_eq_of_p5_eq_one (p5_EVec_eq_one hu hs)]
    ext i
    fin_cases i <;> simp [EVec, normalizedG0Delta1]
    · ring
    · rw [hs_repr]
      ring
  by_cases hks : k <= s
  · let j := k - 1
    have hjlt_s : j < s := by
      dsimp [j]
      omega
    have hjlt_m : j < m - 1 := by omega
    have hk_eq : k = 1 + j := by
      dsimp [j]
      omega
    have hstate : G^[k] w0 = w1 + j • normalizedG0Delta0 m := by
      have hiter : G^[k] w0 = G^[j] (G w0) := by
        rw [hk_eq]
        have h_eq : 1 + j = j + 1 := by omega
        simpa [h_eq] using (Function.iterate_succ_apply' G j w0)
      rw [hiter, hGw0]
      apply normalizedG0Vec_iter_eq_add_delta0_of_coords134
      · dsimp [w1]
        exact hV0
      · intro r hr
        dsimp [w1]
        exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := r) (by omega)
      · intro r hr
        dsimp [w1]
        exact zmod_one_sub_nat_add_nat_ne_zero (m := m) (s := s) (k := r)
          (by omega) hsm
    have h3ne : (G^[k] w0) 3 ≠ 0 := by
      rw [hstate]
      dsimp [w1]
      simp [normalizedG0Delta0]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := j) hjlt_m
    simpa [G, w0] using p5_ne_two_of_three_ne_zero h3ne
  · let n1 := s - 1
    let j := k - (s + 1)
    let w2 : Vec5 m :=
      ![
        u - 3 + ((s - 1 : Nat) : ZMod m) * (-2 : ZMod m) - 3,
        v + 1,
        0,
        (s : ZMod m) + 2,
        1
      ]
    have hjlt : j < m - s - 2 := by
      dsimp [j]
      omega
    have hk_eq : k = j + (1 + (n1 + 1)) := by
      dsimp [j, n1]
      omega
    have hw1run : G^[n1] w1 = w1 + n1 • normalizedG0Delta0 m := by
      dsimp [G]
      apply normalizedG0Vec_iter_eq_add_delta0_of_coords134
      · dsimp [w1]
        exact hV0
      · intro r hr
        dsimp [w1]
        exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := r) (by omega)
      · intro r hr
        dsimp [w1]
        exact zmod_one_sub_nat_add_nat_ne_zero (m := m) (s := s) (k := r)
          (by simpa [n1] using hr) hsm
    have hp3 : p5 (G^[n1] w1) = 3 := by
      rw [hw1run]
      apply p5_eq_three_of_one_three_ne_zero_two_four_zero
      · dsimp [w1, n1]
        simp [normalizedG0Delta0]
        simpa [normalizedG0Delta0] using hV0
      · dsimp [w1, n1]
        intro h
        have hsne : ((s : Nat) : ZMod m) ≠ 0 := by
          apply zmod_nat_ne_zero (m := m) (k := s) <;> omega
        apply hsne
        have h' : (1 : ZMod m) + (((s - 1 : Nat) : ZMod m)) = 0 := by
          simpa [normalizedG0Delta0] using h
        simpa [zmod_one_add_nat_pred m s hspos] using h'
      · dsimp [w1, n1]
        simp [normalizedG0Delta0]
      · dsimp [w1, n1]
        simp [normalizedG0Delta0]
        exact zmod_one_sub_add_nat_pred m s hspos
    have hAfter3 : G (G^[n1] w1) = w2 := by
      have hp3' : p5 (w1 + n1 • normalizedG0Delta0 m) = 3 := by
        simpa [hw1run] using hp3
      rw [hw1run]
      dsimp [G]
      rw [normalizedG0Vec_eq_of_p5_eq_three hp3']
      dsimp [w1, w2, n1]
      ext i
      fin_cases i <;> simp [normalizedG0Delta0, normalizedG0Delta3]
      · rw [zmod_nat_pred_eq_sub_one (m := m) (s := s) hspos]
        ring
      · rw [zmod_nat_pred_eq_sub_one (m := m) (s := s) hspos]
        ring
      · rw [zmod_nat_pred_eq_sub_one (m := m) (s := s) hspos]
        ring
    have hw2run : G^[j] w2 = w2 + j • normalizedG0Delta0 m := by
      dsimp [G]
      apply normalizedG0Vec_iter_eq_add_delta0_of_coords134
      · dsimp [w2]
        exact hV0
      · intro r hr
        dsimp [w2]
        exact zmod_nat_add_two_add_nat_ne_zero (m := m) (s := s) (k := r)
          (by omega)
      · intro r hr
        dsimp [w2]
        exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := r) (by omega)
    have hstate : G^[k] w0 = w2 + j • normalizedG0Delta0 m := by
      have hiter : G^[k] w0 = G^[j] (G (G^[n1] (G w0))) := by
        simpa [hk_eq] using (iterate_decomp4 G w0 n1 j)
      rw [hiter, hGw0, hAfter3, hw2run]
    have h3ne : (G^[k] w0) 3 ≠ 0 := by
      rw [hstate]
      dsimp [w2]
      simp [normalizedG0Delta0]
      exact zmod_nat_add_two_add_nat_ne_zero (m := m) (s := s) (k := j) hjlt
    simpa [G, w0] using p5_ne_two_of_three_ne_zero h3ne

theorem normalizedG0Vec_E_seam {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h)
    {u : ZMod m} (hu : u ≠ 0) :
    ((normalizedG0Vec (m := m))^[3 * m - 2]) (EVec u (-u - 1)) =
      EVec (u + 1) (-u) := by
  let G := normalizedG0Vec (m := m)
  let w0 : Vec5 m := EVec u (-u - 1)
  let w1 : Vec5 m := ![u - 3, -u, 0, 1, (2 : ZMod m)]
  have hneg_u : -u ≠ 0 := by
    intro h
    exact hu (neg_eq_zero.mp h)
  have hs : u + (-u - 1 : ZMod m) ≠ 0 := by
    have hne : (-1 : ZMod m) ≠ 0 := by
      simpa using zmod_neg_nat_ne_zero (m := m) (n := 1) (by omega) (by omega)
    intro h
    apply hne
    linear_combination h
  have hGw0 : G w0 = w1 := by
    dsimp [G, w0, w1]
    rw [normalizedG0Vec_eq_of_p5_eq_one (p5_EVec_eq_one hu hs)]
    ext i
    fin_cases i <;> simp [EVec, normalizedG0Delta1]
    all_goals ring
  let nA := m - 2
  let nB := m - 1
  have hw1run : G^[nA] w1 = w1 + nA • normalizedG0Delta0 m := by
    dsimp [G]
    apply normalizedG0Vec_iter_eq_add_delta0_of_coords134
    · dsimp [w1]
      exact hneg_u
    · intro k hk
      dsimp [w1]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := k) (by omega)
    · intro k hk
      dsimp [w1]
      exact zmod_two_add_nat_ne_zero_before_mod (m := m) (k := k) (by simpa [nA] using hk)
  have hp3a : p5 (G^[nA] w1) = 3 := by
    rw [hw1run]
    apply p5_eq_three_of_one_three_ne_zero_two_four_zero
    · dsimp [w1, nA]
      simpa [normalizedG0Delta0] using hneg_u
    · dsimp [w1, nA]
      have hne : ((m - 1 : Nat) : ZMod m) ≠ 0 := by
        apply zmod_nat_ne_zero (m := m) (k := m - 1) <;> omega
      intro h
      apply hne
      have h' : (1 : ZMod m) + (((m - 2 : Nat) : ZMod m)) = 0 := by
        simpa [normalizedG0Delta0] using h
      have hpred : (1 : ZMod m) + (((m - 2 : Nat) : ZMod m)) =
          ((m - 1 : Nat) : ZMod m) := by
        rw [zmod_nat_sub_two_self_eq_neg_two (m := m) (by omega)]
        rw [zmod_nat_pred_self_eq_neg_one (m := m)]
        ring
      simpa [hpred] using h'
    · dsimp [w1, nA]
      simp [normalizedG0Delta0]
    · dsimp [w1, nA]
      simp [normalizedG0Delta0]
      exact zmod_two_add_nat_sub_two_self (m := m) (by omega)
  let w2 : Vec5 m := ![u - 2, -u, 0, 1, (1 : ZMod m)]
  have hAfterA : G (G^[nA] w1) = w2 := by
    have hp3a' : p5 (w1 + nA • normalizedG0Delta0 m) = 3 := by
      simpa [hw1run] using hp3a
    rw [hw1run]
    dsimp [G]
    rw [normalizedG0Vec_eq_of_p5_eq_three hp3a']
    dsimp [w1, w2, nA]
    ext i
    fin_cases i <;> simp [normalizedG0Delta0, normalizedG0Delta3]
    · rw [zmod_nat_sub_two_self_eq_neg_two (m := m) (by omega)]
      ring
    · rw [zmod_nat_sub_two_self_eq_neg_two (m := m) (by omega)]
      ring
    · rw [zmod_nat_sub_two_self_eq_neg_two (m := m) (by omega)]
      ring
  have hw2run : G^[nB] w2 = w2 + nB • normalizedG0Delta0 m := by
    dsimp [G]
    apply normalizedG0Vec_iter_eq_add_delta0_of_coords134
    · dsimp [w2]
      exact hneg_u
    · intro k hk
      dsimp [w2]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := k) (by simpa [nB] using hk)
    · intro k hk
      dsimp [w2]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := k) (by simpa [nB] using hk)
  have hp3b : p5 (G^[nB] w2) = 3 := by
    rw [hw2run]
    apply p5_eq_three_of_zero_one_ne_two_three_four_zero
    · dsimp [w2, nB]
      simpa [normalizedG0Delta0, zmod_nat_pred_self_eq_neg_one (m := m)] using hu
    · dsimp [w2, nB]
      simpa [normalizedG0Delta0] using hneg_u
    · dsimp [w2, nB]
      simp [normalizedG0Delta0]
    · dsimp [w2, nB]
      simp [normalizedG0Delta0]
      exact zmod_one_add_nat_pred_self (m := m)
    · dsimp [w2, nB]
      simp [normalizedG0Delta0]
      exact zmod_one_add_nat_pred_self (m := m)
  let w3 : Vec5 m := ![u - 3, -u, 0, 2, (1 : ZMod m)]
  have hAfterB : G (G^[nB] w2) = w3 := by
    have hp3b' : p5 (w2 + nB • normalizedG0Delta0 m) = 3 := by
      simpa [hw2run] using hp3b
    rw [hw2run]
    dsimp [G]
    rw [normalizedG0Vec_eq_of_p5_eq_three hp3b']
    dsimp [w2, w3, nB]
    ext i
    fin_cases i <;> simp [normalizedG0Delta0, normalizedG0Delta3]
    · rw [zmod_nat_pred_self_eq_neg_one (m := m)]
      ring
    · exact zmod_one_add_nat_pred_self (m := m)
    · exact zmod_one_add_nat_pred_self (m := m)
  have hw3run : G^[nA] w3 = w3 + nA • normalizedG0Delta0 m := by
    dsimp [G]
    apply normalizedG0Vec_iter_eq_add_delta0_of_coords134
    · dsimp [w3]
      exact hneg_u
    · intro k hk
      dsimp [w3]
      exact zmod_two_add_nat_ne_zero_before_mod (m := m) (k := k) (by simpa [nA] using hk)
    · intro k hk
      dsimp [w3]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := k) (by omega)
  have htime : 3 * m - 2 = nA + (1 + (nB + (1 + (nA + 1)))) := by
    omega
  have hiter :
      G^[3 * m - 2] w0 = G^[nA] (G (G^[nB] (G (G^[nA] (G w0))))) := by
    have htail : G^[nB + (1 + (nA + 1))] w0 =
        G^[nB] (G (G^[nA] (G w0))) := by
      simpa using (iterate_decomp4 G w0 nA nB)
    have houter :
        G^[nA + (1 + (nB + (1 + (nA + 1))))] w0 =
          G^[nA] (G (G^[nB + (1 + (nA + 1))] w0)) := by
      rw [Function.iterate_add_apply]
      congr
      have hsucc :
          1 + (nB + (1 + (nA + 1))) = Nat.succ (nB + (1 + (nA + 1))) := by
        omega
      rw [hsucc]
      exact Function.iterate_succ_apply' G (nB + (1 + (nA + 1))) w0
    calc
      G^[3 * m - 2] w0 =
          G^[nA + (1 + (nB + (1 + (nA + 1))))] w0 := by rw [htime]
      _ = G^[nA] (G (G^[nB + (1 + (nA + 1))] w0)) := houter
      _ = G^[nA] (G (G^[nB] (G (G^[nA] (G w0))))) := by
        rw [htail]
  change G^[3 * m - 2] w0 = EVec (u + 1) (-u)
  rw [hiter, hGw0, hAfterA, hAfterB, hw3run]
  dsimp [w3, nA]
  ext i
  fin_cases i <;> simp [EVec, normalizedG0Delta0]
  · rw [zmod_nat_sub_two_self_eq_neg_two (m := m) (by omega)]
    ring
  · rw [zmod_nat_sub_two_self_eq_neg_two (m := m) (by omega)]
    ring
  · rw [zmod_nat_sub_two_self_eq_neg_two (m := m) (by omega)]
    ring

theorem normalizedG0Vec_E_seam_p5_no_earlier {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h)
    {u : ZMod m} (hu : u ≠ 0) :
    forall k : Nat, 0 < k -> k < 3 * m - 2 ->
      p5 (((normalizedG0Vec (m := m))^[k]) (EVec u (-u - 1))) ≠ 2 := by
  intro k hkpos hklt
  let G := normalizedG0Vec (m := m)
  let w0 : Vec5 m := EVec u (-u - 1)
  let w1 : Vec5 m := ![u - 3, -u, 0, 1, (2 : ZMod m)]
  let nA := m - 2
  let nB := m - 1
  have hneg_u : -u ≠ 0 := by
    intro h
    exact hu (neg_eq_zero.mp h)
  have hs : u + (-u - 1 : ZMod m) ≠ 0 := by
    have hne : (-1 : ZMod m) ≠ 0 := by
      simpa using zmod_neg_nat_ne_zero (m := m) (n := 1) (by omega) (by omega)
    intro h
    apply hne
    linear_combination h
  have hGw0 : G w0 = w1 := by
    dsimp [G, w0, w1]
    rw [normalizedG0Vec_eq_of_p5_eq_one (p5_EVec_eq_one hu hs)]
    ext i
    fin_cases i <;> simp [EVec, normalizedG0Delta1]
    all_goals ring
  by_cases hk_first : k <= m - 1
  · let j := k - 1
    have hjlt : j < m - 1 := by
      dsimp [j]
      omega
    have hk_eq : k = 1 + j := by
      dsimp [j]
      omega
    have hstate : G^[k] w0 = w1 + j • normalizedG0Delta0 m := by
      have hiter : G^[k] w0 = G^[j] (G w0) := by
        rw [hk_eq]
        have h_eq : 1 + j = j + 1 := by omega
        simpa [h_eq] using (Function.iterate_succ_apply' G j w0)
      rw [hiter, hGw0]
      apply normalizedG0Vec_iter_eq_add_delta0_of_coords134
      · dsimp [w1]
        exact hneg_u
      · intro r hr
        dsimp [w1]
        exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := r) (by omega)
      · intro r hr
        dsimp [w1]
        exact zmod_two_add_nat_ne_zero_before_mod (m := m) (k := r) (by omega)
    have h3ne : (G^[k] w0) 3 ≠ 0 := by
      rw [hstate]
      dsimp [w1]
      simp [normalizedG0Delta0]
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := j) hjlt
    simpa [G, w0] using p5_ne_two_of_three_ne_zero h3ne
  · by_cases hk_second : k <= 2 * m - 1
    · let j := k - m
      let w2 : Vec5 m := ![u - 2, -u, 0, 1, (1 : ZMod m)]
      have hjle : j <= nB := by
        dsimp [j, nB]
        omega
      have hk_eq : k = j + (1 + (nA + 1)) := by
        dsimp [j, nA]
        omega
      have hw1run : G^[nA] w1 = w1 + nA • normalizedG0Delta0 m := by
        dsimp [G]
        apply normalizedG0Vec_iter_eq_add_delta0_of_coords134
        · dsimp [w1]
          exact hneg_u
        · intro r hr
          dsimp [w1]
          exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := r) (by omega)
        · intro r hr
          dsimp [w1]
          exact zmod_two_add_nat_ne_zero_before_mod (m := m) (k := r)
            (by simpa [nA] using hr)
      have hp3a : p5 (G^[nA] w1) = 3 := by
        rw [hw1run]
        apply p5_eq_three_of_one_three_ne_zero_two_four_zero
        · dsimp [w1, nA]
          simpa [normalizedG0Delta0] using hneg_u
        · dsimp [w1, nA]
          have hne : ((m - 1 : Nat) : ZMod m) ≠ 0 := by
            apply zmod_nat_ne_zero (m := m) (k := m - 1) <;> omega
          intro h
          apply hne
          have h' : (1 : ZMod m) + (((m - 2 : Nat) : ZMod m)) = 0 := by
            simpa [normalizedG0Delta0] using h
          have hpred : (1 : ZMod m) + (((m - 2 : Nat) : ZMod m)) =
              ((m - 1 : Nat) : ZMod m) := by
            rw [zmod_nat_sub_two_self_eq_neg_two (m := m) (by omega)]
            rw [zmod_nat_pred_self_eq_neg_one (m := m)]
            ring
          simpa [hpred] using h'
        · dsimp [w1, nA]
          simp [normalizedG0Delta0]
        · dsimp [w1, nA]
          simp [normalizedG0Delta0]
          exact zmod_two_add_nat_sub_two_self (m := m) (by omega)
      have hAfterA : G (G^[nA] w1) = w2 := by
        have hp3a' : p5 (w1 + nA • normalizedG0Delta0 m) = 3 := by
          simpa [hw1run] using hp3a
        rw [hw1run]
        dsimp [G]
        rw [normalizedG0Vec_eq_of_p5_eq_three hp3a']
        dsimp [w1, w2, nA]
        ext i
        fin_cases i <;> simp [normalizedG0Delta0, normalizedG0Delta3]
        · rw [zmod_nat_sub_two_self_eq_neg_two (m := m) (by omega)]
          ring
        · rw [zmod_nat_sub_two_self_eq_neg_two (m := m) (by omega)]
          ring
        · rw [zmod_nat_sub_two_self_eq_neg_two (m := m) (by omega)]
          ring
      have hw2run : G^[j] w2 = w2 + j • normalizedG0Delta0 m := by
        dsimp [G]
        apply normalizedG0Vec_iter_eq_add_delta0_of_coords134
        · dsimp [w2]
          exact hneg_u
        · intro r hr
          dsimp [w2]
          exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := r) (by omega)
        · intro r hr
          dsimp [w2]
          exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := r) (by omega)
      have hstate : G^[k] w0 = w2 + j • normalizedG0Delta0 m := by
        have hiter : G^[k] w0 = G^[j] (G (G^[nA] (G w0))) := by
          simpa [hk_eq] using (iterate_decomp4 G w0 nA j)
        rw [hiter, hGw0, hAfterA, hw2run]
      by_cases hjlast : j = nB
      · have h4zero : (G^[k] w0) 4 = 0 := by
          rw [hstate]
          dsimp [w2, nB] at hjlast ⊢
          simp [normalizedG0Delta0, hjlast]
          exact zmod_one_add_nat_pred_self (m := m)
        simpa [G, w0] using p5_ne_two_of_four_zero h4zero
      · have hjlt : j < nB := by omega
        have h3ne : (G^[k] w0) 3 ≠ 0 := by
          rw [hstate]
          dsimp [w2]
          simp [normalizedG0Delta0]
          exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := j)
            (by simpa [nB] using hjlt)
        simpa [G, w0] using p5_ne_two_of_three_ne_zero h3ne
    · let j := k - 2 * m
      let w2 : Vec5 m := ![u - 2, -u, 0, 1, (1 : ZMod m)]
      let w3 : Vec5 m := ![u - 3, -u, 0, 2, (1 : ZMod m)]
      have hjlt : j < nA := by
        dsimp [j, nA]
        omega
      have hk_eq : k = j + (1 + (nB + (1 + (nA + 1)))) := by
        dsimp [j, nA, nB]
        omega
      have hw1run : G^[nA] w1 = w1 + nA • normalizedG0Delta0 m := by
        dsimp [G]
        apply normalizedG0Vec_iter_eq_add_delta0_of_coords134
        · dsimp [w1]
          exact hneg_u
        · intro r hr
          dsimp [w1]
          exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := r) (by omega)
        · intro r hr
          dsimp [w1]
          exact zmod_two_add_nat_ne_zero_before_mod (m := m) (k := r)
            (by simpa [nA] using hr)
      have hp3a : p5 (G^[nA] w1) = 3 := by
        rw [hw1run]
        apply p5_eq_three_of_one_three_ne_zero_two_four_zero
        · dsimp [w1, nA]
          simpa [normalizedG0Delta0] using hneg_u
        · dsimp [w1, nA]
          have hne : ((m - 1 : Nat) : ZMod m) ≠ 0 := by
            apply zmod_nat_ne_zero (m := m) (k := m - 1) <;> omega
          intro h
          apply hne
          have h' : (1 : ZMod m) + (((m - 2 : Nat) : ZMod m)) = 0 := by
            simpa [normalizedG0Delta0] using h
          have hpred : (1 : ZMod m) + (((m - 2 : Nat) : ZMod m)) =
              ((m - 1 : Nat) : ZMod m) := by
            rw [zmod_nat_sub_two_self_eq_neg_two (m := m) (by omega)]
            rw [zmod_nat_pred_self_eq_neg_one (m := m)]
            ring
          simpa [hpred] using h'
        · dsimp [w1, nA]
          simp [normalizedG0Delta0]
        · dsimp [w1, nA]
          simp [normalizedG0Delta0]
          exact zmod_two_add_nat_sub_two_self (m := m) (by omega)
      have hAfterA : G (G^[nA] w1) = w2 := by
        have hp3a' : p5 (w1 + nA • normalizedG0Delta0 m) = 3 := by
          simpa [hw1run] using hp3a
        rw [hw1run]
        dsimp [G]
        rw [normalizedG0Vec_eq_of_p5_eq_three hp3a']
        dsimp [w1, w2, nA]
        ext i
        fin_cases i <;> simp [normalizedG0Delta0, normalizedG0Delta3]
        · rw [zmod_nat_sub_two_self_eq_neg_two (m := m) (by omega)]
          ring
        · rw [zmod_nat_sub_two_self_eq_neg_two (m := m) (by omega)]
          ring
        · rw [zmod_nat_sub_two_self_eq_neg_two (m := m) (by omega)]
          ring
      have hw2run : G^[nB] w2 = w2 + nB • normalizedG0Delta0 m := by
        dsimp [G]
        apply normalizedG0Vec_iter_eq_add_delta0_of_coords134
        · dsimp [w2]
          exact hneg_u
        · intro r hr
          dsimp [w2]
          exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := r)
            (by simpa [nB] using hr)
        · intro r hr
          dsimp [w2]
          exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := r)
            (by simpa [nB] using hr)
      have hp3b : p5 (G^[nB] w2) = 3 := by
        rw [hw2run]
        apply p5_eq_three_of_zero_one_ne_two_three_four_zero
        · dsimp [w2, nB]
          simpa [normalizedG0Delta0, zmod_nat_pred_self_eq_neg_one (m := m)] using hu
        · dsimp [w2, nB]
          simpa [normalizedG0Delta0] using hneg_u
        · dsimp [w2, nB]
          simp [normalizedG0Delta0]
        · dsimp [w2, nB]
          simp [normalizedG0Delta0]
          exact zmod_one_add_nat_pred_self (m := m)
        · dsimp [w2, nB]
          simp [normalizedG0Delta0]
          exact zmod_one_add_nat_pred_self (m := m)
      have hAfterB : G (G^[nB] w2) = w3 := by
        have hp3b' : p5 (w2 + nB • normalizedG0Delta0 m) = 3 := by
          simpa [hw2run] using hp3b
        rw [hw2run]
        dsimp [G]
        rw [normalizedG0Vec_eq_of_p5_eq_three hp3b']
        dsimp [w2, w3, nB]
        ext i
        fin_cases i <;> simp [normalizedG0Delta0, normalizedG0Delta3]
        · rw [zmod_nat_pred_self_eq_neg_one (m := m)]
          ring
        · exact zmod_one_add_nat_pred_self (m := m)
        · exact zmod_one_add_nat_pred_self (m := m)
      have hw3run : G^[j] w3 = w3 + j • normalizedG0Delta0 m := by
        dsimp [G]
        apply normalizedG0Vec_iter_eq_add_delta0_of_coords134
        · dsimp [w3]
          exact hneg_u
        · intro r hr
          dsimp [w3]
          exact zmod_two_add_nat_ne_zero_before_mod (m := m) (k := r) (by omega)
        · intro r hr
          dsimp [w3]
          exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := r) (by omega)
      have hstate : G^[k] w0 = w3 + j • normalizedG0Delta0 m := by
        have htail : G^[nB + (1 + (nA + 1))] w0 =
            G^[nB] (G (G^[nA] (G w0))) := by
          simpa using (iterate_decomp4 G w0 nA nB)
        have houter :
            G^[j + (1 + (nB + (1 + (nA + 1))))] w0 =
              G^[j] (G (G^[nB + (1 + (nA + 1))] w0)) := by
          rw [Function.iterate_add_apply]
          congr
          have hsucc :
              1 + (nB + (1 + (nA + 1))) =
                Nat.succ (nB + (1 + (nA + 1))) := by
            omega
          rw [hsucc]
          exact Function.iterate_succ_apply' G (nB + (1 + (nA + 1))) w0
        calc
          G^[k] w0 =
              G^[j + (1 + (nB + (1 + (nA + 1))))] w0 := by rw [hk_eq]
          _ = G^[j] (G (G^[nB + (1 + (nA + 1))] w0)) := houter
          _ = G^[j] (G (G^[nB] (G (G^[nA] (G w0))))) := by rw [htail]
          _ = w3 + j • normalizedG0Delta0 m := by
            rw [hGw0, hAfterA, hAfterB, hw3run]
      have h3ne : (G^[k] w0) 3 ≠ 0 := by
        rw [hstate]
        dsimp [w3]
        simp [normalizedG0Delta0]
        exact zmod_two_add_nat_ne_zero_before_mod (m := m) (k := j)
          (by simpa [nA] using hjlt)
      simpa [G, w0] using p5_ne_two_of_three_ne_zero h3ne

abbrev LongIdx (m : Nat) := Fin (m - 1) × Fin (m - 1)

def longU {m : Nat} (I : LongIdx m) : ZMod m :=
  (I.1.val + 1 : Nat)

def longV {m : Nat} (I : LongIdx m) : ZMod m :=
  (I.2.val + 1 : Nat) - longU I

def longE {m : Nat} (I : LongIdx m) : Vec5 m :=
  EVec (longU I) (longV I)

def longStepTime (m : Nat) (I : LongIdx m) : Nat :=
  if I.2.val + 1 = m - 1 then
    3 * m - 2
  else if I.2.val + 1 = I.1.val then
    m
  else
    m - 1

def longIdxSucc? {m : Nat} (I : LongIdx m) : Option (LongIdx m) :=
  if ht : I.2.val + 1 < m - 1 then
    some (I.1, ⟨I.2.val + 1, ht⟩)
  else if hq : I.1.val + 1 < m - 1 then
    some (⟨I.1.val + 1, hq⟩, ⟨0, by omega⟩)
  else
    none

def longStart (m : Nat) (hm1 : 0 < m - 1) : LongIdx m :=
  (⟨0, hm1⟩, ⟨0, hm1⟩)

def longIdxAfter (m : Nat) (hm1 : 0 < m - 1) : Nat -> Option (LongIdx m)
  | 0 => some (longStart m hm1)
  | n + 1 =>
      match longIdxAfter m hm1 n with
      | some I => longIdxSucc? I
      | none => none

def longPrefixTime (m : Nat) (hm1 : 0 < m - 1) : Nat -> Nat
  | 0 => 0
  | n + 1 =>
      match longIdxAfter m hm1 n with
      | some I => longStepTime m I + longPrefixTime m hm1 n
      | none => longPrefixTime m hm1 n

theorem longIdxAfter_row_col {m r c : Nat} (hm1 : 0 < m - 1)
    (hr : r < m - 1) (hc : c < m - 1) :
    longIdxAfter m hm1 (r * (m - 1) + c) =
      some ((⟨r, hr⟩ : Fin (m - 1)), (⟨c, hc⟩ : Fin (m - 1))) := by
  induction r generalizing c with
  | zero =>
      induction c with
      | zero =>
          simp [longIdxAfter, longStart]
      | succ c ih =>
          have hc' : c < m - 1 := by omega
          have hstep : c + 1 < m - 1 := hc
          rw [show 0 * (m - 1) + (c + 1) = (0 * (m - 1) + c) + 1 by omega]
          dsimp [longIdxAfter]
          rw [ih hc']
          simp [longIdxSucc?, hstep]
  | succ r ih =>
      induction c with
      | zero =>
          have hr' : r < m - 1 := by omega
          let last : Nat := m - 2
          have hlast : last < m - 1 := by
            dsimp [last]
            omega
          have hlast_add : last + 1 = m - 1 := by
            dsimp [last]
            omega
          have hidx : (r + 1) * (m - 1) + 0 =
              (r * (m - 1) + last) + 1 := by
            calc
              (r + 1) * (m - 1) + 0 = r * (m - 1) + (m - 1) := by
                rw [Nat.succ_mul]
                omega
              _ = (r * (m - 1) + last) + 1 := by omega
          rw [hidx]
          dsimp [longIdxAfter]
          rw [ih (c := last) hr' hlast]
          have hnotCol : ¬ last + 1 < m - 1 := by
            dsimp [last]
            omega
          have hrow : r + 1 < m - 1 := hr
          simp [longIdxSucc?, hnotCol, hrow]
      | succ c ihc =>
          have hc' : c < m - 1 := by omega
          have hstep : c + 1 < m - 1 := hc
          rw [show (r + 1) * (m - 1) + (c + 1) =
              ((r + 1) * (m - 1) + c) + 1 by omega]
          dsimp [longIdxAfter]
          rw [ihc hc']
          simp [longIdxSucc?, hstep]

theorem longIdxAfter_end {m : Nat} (hm1 : 0 < m - 1) :
    longIdxAfter m hm1 ((m - 1) * (m - 1)) = none := by
  let last : Nat := m - 2
  have hlast : last < m - 1 := by
    dsimp [last]
    omega
  have hlast_add : last + 1 = m - 1 := by
    dsimp [last]
    omega
  have hidx : (m - 1) * (m - 1) =
      (last * (m - 1) + last) + 1 := by
    calc
      (m - 1) * (m - 1) = (last + 1) * (m - 1) := by rw [hlast_add]
      _ = last * (m - 1) + (m - 1) := by rw [Nat.succ_mul]
      _ = (last * (m - 1) + last) + 1 := by omega
  rw [hidx]
  dsimp [longIdxAfter]
  rw [longIdxAfter_row_col hm1 hlast hlast]
  have hnotCol : ¬ last + 1 < m - 1 := by
    dsimp [last]
    omega
  have hnotRow : ¬ last + 1 < m - 1 := by
    dsimp [last]
    omega
  simp [longIdxSucc?, hnotCol, hnotRow]

def longRowPrefixClosed (m r c : Nat) : Nat :=
  c * (m - 1) + (if 0 < r ∧ r <= c then 1 else 0) +
    (if m - 1 <= c then 2 * m - 1 else 0)

theorem longStepTime_row_col {m r c : Nat}
    (hr : r < m - 1) (hc : c < m - 1) :
    longStepTime m ((⟨r, hr⟩ : Fin (m - 1)), (⟨c, hc⟩ : Fin (m - 1))) =
      if c + 1 = m - 1 then
        3 * m - 2
      else if c + 1 = r then
        m
      else
        m - 1 := by
  simp [longStepTime]

theorem longRowPrefixClosed_succ {m r c : Nat}
    (hm5 : 5 <= m) (hr : r < m - 1) (hc : c + 1 <= m - 1) :
    longRowPrefixClosed m r (c + 1) =
      (if c + 1 = m - 1 then
        3 * m - 2
      else if c + 1 = r then
        m
      else
        m - 1) + longRowPrefixClosed m r c := by
  unfold longRowPrefixClosed
  have hsucc_mul : (c + 1) * (m - 1) = c * (m - 1) + (m - 1) := by
    rw [Nat.succ_mul]
  by_cases hseam : c + 1 = m - 1
  · have hnotPrevSeam : ¬ m - 1 <= c := by omega
    have hnextSeam : m - 1 <= c + 1 := by omega
    have hnotQuickStep : ¬ c + 1 = r := by omega
    have hquickPrevIff : (0 < r ∧ r <= c + 1) ↔ (0 < r ∧ r <= c) := by
      omega
    have hquickEndIff : (0 < r ∧ r <= m - 1) ↔ (0 < r ∧ r <= c) := by
      omega
    have hrle : r <= m - 1 := by omega
    have hsq : (m - 1) * (m - 1) = c * (m - 1) + (m - 1) := by
      calc
        (m - 1) * (m - 1) = (c + 1) * (m - 1) := by rw [hseam]
        _ = c * (m - 1) + (m - 1) := hsucc_mul
    by_cases hprev : 0 < r ∧ r <= c
    · have hnext : 0 < r ∧ r <= c + 1 := hquickPrevIff.mpr hprev
      have hend : 0 < r ∧ r <= m - 1 := hquickEndIff.mpr hprev
      simp [hseam, hnotQuickStep, hnotPrevSeam, hnextSeam, hprev, hnext,
        hend, hrle]
      omega
    · have hnext : ¬ (0 < r ∧ r <= c + 1) := by
        simpa [hquickPrevIff] using hprev
      have hend : ¬ (0 < r ∧ r <= m - 1) := by
        simpa [hquickEndIff] using hprev
      have hnotPos : ¬ 0 < r := by omega
      simp [hseam, hnotQuickStep, hnotPrevSeam, hnextSeam, hprev, hnext,
        hend, hrle, hnotPos]
      omega
  · have hnotPrevSeam : ¬ m - 1 <= c := by omega
    have hnotNextSeam : ¬ m - 1 <= c + 1 := by omega
    by_cases hquick : c + 1 = r
    · have hprev : ¬ (0 < r ∧ r <= c) := by omega
      have hnext : 0 < r ∧ r <= c + 1 := by omega
      have hnotREnd : ¬ r = m - 1 := by omega
      have hnotMleR1 : ¬ m <= r + 1 := by omega
      have hnotRleC : ¬ r <= c := by omega
      have hrmul : r * (m - 1) = c * (m - 1) + (m - 1) := by
        calc
          r * (m - 1) = (c + 1) * (m - 1) := by rw [hquick]
          _ = c * (m - 1) + (m - 1) := hsucc_mul
      simp [hseam, hquick, hnotPrevSeam, hnotNextSeam, hprev, hnext,
        hnotREnd, hnotMleR1, hnotRleC]
      omega
    · by_cases hprev : 0 < r ∧ r <= c
      · have hnext : 0 < r ∧ r <= c + 1 := by omega
        simp [hseam, hquick, hnotPrevSeam, hnotNextSeam, hprev, hnext]
        omega
      · have hnext : ¬ (0 < r ∧ r <= c + 1) := by omega
        simp [hseam, hquick, hnotPrevSeam, hnotNextSeam, hprev, hnext]
        omega

theorem longRowPrefixClosed_end {m r : Nat}
    (hm5 : 5 <= m) (hr : r < m - 1) :
    longRowPrefixClosed m r (m - 1) =
      if r = 0 then m ^ 2 else m ^ 2 + 1 := by
  unfold longRowPrefixClosed
  have hseam : m - 1 <= m - 1 := le_rfl
  by_cases hr0 : r = 0
  · have hquick : ¬ (0 < r ∧ r <= m - 1) := by omega
    simp [hr0, hquick, hseam]
    obtain ⟨L, rfl⟩ : ∃ L, m = L + 5 := ⟨m - 5, by omega⟩
    have h1 : L + 5 - 1 = L + 4 := by omega
    rw [h1]
    ring_nf
    omega
  · have hquick : 0 < r ∧ r <= m - 1 := by omega
    simp [hr0, hquick, hseam]
    obtain ⟨L, rfl⟩ : ∃ L, m = L + 5 := ⟨m - 5, by omega⟩
    have h1 : L + 5 - 1 = L + 4 := by omega
    rw [h1]
    ring_nf
    omega

theorem longPrefixTime_row_col {m r c : Nat} (hm1 : 0 < m - 1)
    (hm5 : 5 <= m) (hr : r < m - 1) (hc : c <= m - 1) :
    longPrefixTime m hm1 (r * (m - 1) + c) =
      longRowPrefixClosed m r c + longPrefixTime m hm1 (r * (m - 1)) := by
  induction c with
  | zero =>
      have hnotSeam : ¬ m - 1 <= 0 := by omega
      simp [longRowPrefixClosed, hnotSeam]
      omega
  | succ c ih =>
      have hc' : c <= m - 1 := by omega
      have hclt : c < m - 1 := by omega
      rw [show r * (m - 1) + (c + 1) = (r * (m - 1) + c) + 1 by omega]
      dsimp [longPrefixTime]
      rw [longIdxAfter_row_col hm1 hr hclt]
      change
        longStepTime m ((⟨r, hr⟩ : Fin (m - 1)), (⟨c, hclt⟩ : Fin (m - 1))) +
            longPrefixTime m hm1 (r * (m - 1) + c) =
          longRowPrefixClosed m r (c + 1) + longPrefixTime m hm1 (r * (m - 1))
      rw [longStepTime_row_col (m := m) (r := r) (c := c) hr hclt]
      rw [ih hc']
      rw [longRowPrefixClosed_succ hm5 hr hc]
      omega

theorem longPrefixTime_row_advance {m r : Nat} (hm1 : 0 < m - 1)
    (hm5 : 5 <= m) (hr : r < m - 1) :
    longPrefixTime m hm1 ((r + 1) * (m - 1)) =
      (if r = 0 then m ^ 2 else m ^ 2 + 1) +
        longPrefixTime m hm1 (r * (m - 1)) := by
  have hrow := longPrefixTime_row_col (m := m) (r := r) (c := m - 1)
    hm1 hm5 hr le_rfl
  have hidx : r * (m - 1) + (m - 1) = (r + 1) * (m - 1) := by
    rw [Nat.succ_mul]
  rw [hidx] at hrow
  rw [longRowPrefixClosed_end hm5 hr] at hrow
  exact hrow

theorem longPrefixTime_row_start {m r : Nat} (hm1 : 0 < m - 1)
    (hm5 : 5 <= m) (hr : r <= m - 1) :
    longPrefixTime m hm1 (r * (m - 1)) =
      if r = 0 then 0 else r * m ^ 2 + r - 1 := by
  induction r with
  | zero =>
      simp [longPrefixTime]
  | succ r ih =>
      have hr' : r <= m - 1 := by omega
      have hrlt : r < m - 1 := by omega
      rw [longPrefixTime_row_advance hm1 hm5 hrlt]
      rw [ih hr']
      by_cases hr0 : r = 0
      · subst r
        simp
      · have hsucc_ne : ¬ r + 1 = 0 := by omega
        simp [hr0, hsucc_ne]
        rw [Nat.succ_mul]
        omega

theorem longPrefixTime_end {m : Nat} (hm1 : 0 < m - 1) (hm5 : 5 <= m) :
    longPrefixTime m hm1 ((m - 1) * (m - 1)) =
      (m - 1) * m ^ 2 + (m - 1) - 1 := by
  have hrow := longPrefixTime_row_start (m := m) (r := m - 1) hm1 hm5 le_rfl
  have hne : ¬ m - 1 = 0 := by omega
  simpa [hne] using hrow

theorem last_zero_total_time_eq {m : Nat} (hm5 : 5 <= m) :
    2 * m + ((m - 1) * m ^ 2 + (m - 1) - 1) =
      m ^ 3 - (m - 1) * (m - 2) := by
  obtain ⟨L, rfl⟩ : ∃ L, m = L + 5 := ⟨m - 5, by omega⟩
  have h1 : L + 5 - 1 = L + 4 := by omega
  have h2 : L + 5 - 2 = L + 3 := by omega
  rw [h1, h2]
  ring_nf
  omega

theorem zmod_nat_eq_of_lt {m a b : Nat} [NeZero m]
    (ha : a < m) (hb : b < m)
    (h : ((a : Nat) : ZMod m) = ((b : Nat) : ZMod m)) :
    a = b := by
  have hmod : a % m = b % m := (ZMod.natCast_eq_natCast_iff' a b m).1 h
  simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hmod

theorem longU_ne_zero {m : Nat} [NeZero m] (hm5 : 5 <= m) (I : LongIdx m) :
    longU I ≠ 0 := by
  dsimp [longU]
  apply zmod_nat_ne_zero (m := m) (k := I.1.val + 1) <;> omega

theorem long_sum_ne_zero {m : Nat} [NeZero m] (hm5 : 5 <= m) (I : LongIdx m) :
    longU I + longV I ≠ 0 := by
  have hne : (((I.2.val + 1 : Nat) : ZMod m)) ≠ 0 := by
    apply zmod_nat_ne_zero (m := m) (k := I.2.val + 1) <;> omega
  intro h
  apply hne
  dsimp [longU, longV] at h ⊢
  linear_combination h

theorem p5_longE_eq_one {m : Nat} [NeZero m] (hm5 : 5 <= m) (I : LongIdx m) :
    p5 (longE I) = 1 := by
  dsimp [longE]
  exact p5_EVec_eq_one (longU_ne_zero hm5 I) (long_sum_ne_zero hm5 I)

theorem p5_longE_ne_two {m : Nat} [NeZero m] (hm5 : 5 <= m) (I : LongIdx m) :
    p5 (longE I) ≠ 2 := by
  rw [p5_longE_eq_one hm5 I]
  decide

theorem longV_eq_neg_one_of_quick {m : Nat} [NeZero m] {I : LongIdx m}
    (hquick : I.2.val + 1 = I.1.val) :
    longV I = -1 := by
  dsimp [longV, longU]
  rw [hquick]
  simp [Nat.cast_add]

theorem longU_ne_one_of_quick {m : Nat} [NeZero m] (hm5 : 5 <= m)
    {I : LongIdx m} (hquick : I.2.val + 1 = I.1.val) :
    longU I ≠ 1 := by
  have hqpos : 0 < I.1.val := by omega
  have hqne : (((I.1.val : Nat) : ZMod m)) ≠ 0 := by
    apply zmod_nat_ne_zero (m := m) (k := I.1.val) <;> omega
  intro h
  apply hqne
  have hsub : longU I - 1 = 0 := by rw [h]; ring
  dsimp [longU] at hsub
  simpa [Nat.cast_add] using hsub

theorem longV_add_one_ne_zero_of_not_quick {m : Nat} [NeZero m]
    (hm5 : 5 <= m) {I : LongIdx m}
    (ht : I.2.val + 1 < m - 1) (hquick : ¬ I.2.val + 1 = I.1.val) :
    longV I + 1 ≠ 0 := by
  intro hzero
  have heq : (((I.2.val + 2 : Nat) : ZMod m)) =
      (((I.1.val + 1 : Nat) : ZMod m)) := by
    have hstep : (((I.2.val + 1 : Nat) : ZMod m) + 1) =
        (((I.1.val + 1 : Nat) : ZMod m)) := by
      dsimp [longV, longU] at hzero
      linear_combination hzero
    dsimp [longV, longU] at hzero
    calc
      (((I.2.val + 2 : Nat) : ZMod m))
          = (((I.2.val + 1 : Nat) : ZMod m) + 1) := by
            rw [show I.2.val + 2 = (I.2.val + 1) + 1 by omega]
            rw [Nat.cast_add]
            simp
      _ = (((I.1.val + 1 : Nat) : ZMod m)) := hstep
  have hnat := zmod_nat_eq_of_lt (m := m) (a := I.2.val + 2)
    (b := I.1.val + 1) (by omega) (by omega) heq
  apply hquick
  omega

theorem longV_add_one_ne_neg_longU_of_not_seam {m : Nat} [NeZero m]
    (hm5 : 5 <= m) {I : LongIdx m}
    (ht : I.2.val + 1 < m - 1) :
    longV I + 1 ≠ -longU I := by
  have hne : (((I.2.val + 2 : Nat) : ZMod m)) ≠ 0 := by
    apply zmod_nat_ne_zero (m := m) (k := I.2.val + 2) <;> omega
  intro h
  apply hne
  have hzero : (((I.2.val + 1 : Nat) : ZMod m) + 1) = 0 := by
    dsimp [longV, longU] at h
    linear_combination h
  calc
    (((I.2.val + 2 : Nat) : ZMod m))
        = (((I.2.val + 1 : Nat) : ZMod m) + 1) := by
          rw [show I.2.val + 2 = (I.2.val + 1) + 1 by omega]
          rw [Nat.cast_add]
          simp
    _ = 0 := hzero

theorem longV_eq_seam {m : Nat} [NeZero m] {I : LongIdx m}
    (hseam : I.2.val + 1 = m - 1) :
    longV I = -longU I - 1 := by
  dsimp [longV, longU]
  rw [hseam]
  rw [zmod_nat_pred_self_eq_neg_one (m := m)]
  ring

theorem longE_col_succ {m : Nat} [NeZero m] {I : LongIdx m}
    (ht : I.2.val + 1 < m - 1) :
    longE (I.1, ⟨I.2.val + 1, ht⟩) = EVec (longU I) (longV I + 1) := by
  ext i
  fin_cases i <;> simp [longE, longU, longV, EVec, Nat.cast_add]
  · ring
  · ring

theorem longE_row_succ {m : Nat} [NeZero m] {I : LongIdx m}
    (hq : I.1.val + 1 < m - 1) :
    longE (⟨I.1.val + 1, hq⟩, ⟨0, by omega⟩) =
      EVec (longU I + 1) (-longU I) := by
  ext i
  fin_cases i <;> simp [longE, longU, longV, EVec, Nat.cast_add]

theorem longE_last_eq_sigma {m : Nat} [NeZero m] {I : LongIdx m}
    (hrow : I.1.val + 1 = m - 1) :
    EVec (longU I + 1) (-longU I) = sigmaVec 1 0 := by
  have hU : longU I = -1 := by
    dsimp [longU]
    rw [hrow]
    exact zmod_nat_pred_self_eq_neg_one (m := m)
  ext i
  fin_cases i <;> simp [EVec, sigmaVec, hU]

theorem normalizedG0Vec_longE_step {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h)
    (I : LongIdx m) :
    ((normalizedG0Vec (m := m))^[longStepTime m I]) (longE I) =
      match longIdxSucc? I with
      | some J => longE J
      | none => sigmaVec 1 0 := by
  have hm5 : 5 <= m := by omega
  by_cases hseam : I.2.val + 1 = m - 1
  · have hnotTop : ¬ I.2.val + 1 < m - 1 := by omega
    have hinput : longE I = EVec (longU I) (-longU I - 1) := by
      simp [longE, longV_eq_seam (I := I) hseam]
    by_cases hrow : I.1.val + 1 < m - 1
    · simp [longStepTime, longIdxSucc?, hseam, hnotTop, hrow]
      rw [hinput]
      rw [normalizedG0Vec_E_seam hm hh2 (longU_ne_zero hm5 I)]
      rw [longE_row_succ (I := I) hrow]
    · have hroweq : I.1.val + 1 = m - 1 := by omega
      simp [longStepTime, longIdxSucc?, hseam, hnotTop, hrow]
      rw [hinput]
      rw [normalizedG0Vec_E_seam hm hh2 (longU_ne_zero hm5 I)]
      exact longE_last_eq_sigma (I := I) hroweq
  · have ht : I.2.val + 1 < m - 1 := by omega
    by_cases hquick : I.2.val + 1 = I.1.val
    · have hinput : longE I = EVec (longU I) (-1) := by
        simp [longE, longV_eq_neg_one_of_quick (I := I) hquick]
      have htime : longStepTime m I = m := by
        unfold longStepTime
        rw [if_neg hseam]
        rw [if_pos hquick]
      have hsucc : longIdxSucc? I = some (I.1, ⟨I.2.val + 1, ht⟩) := by
        unfold longIdxSucc?
        rw [dif_pos ht]
      rw [htime, hsucc]
      simp
      rw [hinput]
      rw [normalizedG0Vec_E_quick hm hh2 (longU_ne_zero hm5 I)
        (longU_ne_one_of_quick hm5 (I := I) hquick)]
      rw [longE_col_succ (I := I) ht]
      simp [longV_eq_neg_one_of_quick (I := I) hquick]
    · simp [longStepTime, longIdxSucc?, hseam, ht, hquick]
      change
        ((normalizedG0Vec (m := m))^[m - 1]) (EVec (longU I) (longV I)) =
          longE (I.1, ⟨I.2.val + 1, ht⟩)
      rw [normalizedG0Vec_E_generic hm hh2
        (longU_ne_zero hm5 I)
        (long_sum_ne_zero hm5 I)
        (longV_add_one_ne_zero_of_not_quick hm5 ht hquick)
        (longV_add_one_ne_neg_longU_of_not_seam hm5 ht)]
      rw [longE_col_succ (I := I) ht]

theorem normalizedG0Vec_longE_step_p5_no_earlier {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h)
    (I : LongIdx m) :
    forall k : Nat, 0 < k -> k < longStepTime m I ->
      p5 (((normalizedG0Vec (m := m))^[k]) (longE I)) ≠ 2 := by
  have hm5 : 5 <= m := by omega
  intro k hkpos hklt
  by_cases hseam : I.2.val + 1 = m - 1
  · have hinput : longE I = EVec (longU I) (-longU I - 1) := by
      simp [longE, longV_eq_seam (I := I) hseam]
    have htime : longStepTime m I = 3 * m - 2 := by
      simp [longStepTime, hseam]
    rw [hinput]
    apply normalizedG0Vec_E_seam_p5_no_earlier hm hh2 (longU_ne_zero hm5 I) k hkpos
    rwa [htime] at hklt
  · have ht : I.2.val + 1 < m - 1 := by omega
    by_cases hquick : I.2.val + 1 = I.1.val
    · have hinput : longE I = EVec (longU I) (-1) := by
        simp [longE, longV_eq_neg_one_of_quick (I := I) hquick]
      have htime : longStepTime m I = m := by
        unfold longStepTime
        rw [if_neg hseam]
        rw [if_pos hquick]
      rw [hinput]
      apply normalizedG0Vec_E_quick_p5_no_earlier hm hh2
        (longU_ne_zero hm5 I) (longU_ne_one_of_quick hm5 (I := I) hquick)
        k hkpos
      rwa [htime] at hklt
    · have htime : longStepTime m I = m - 1 := by
        unfold longStepTime
        rw [if_neg hseam]
        rw [if_neg hquick]
      apply normalizedG0Vec_E_generic_p5_no_earlier hm hh2
        (longU_ne_zero hm5 I)
        (long_sum_ne_zero hm5 I)
        (longV_add_one_ne_zero_of_not_quick hm5 ht hquick)
        (longV_add_one_ne_neg_longU_of_not_seam hm5 ht)
        k hkpos
      rwa [htime] at hklt

theorem normalizedG0Vec_last_zero_initial_longE {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    ((normalizedG0Vec (m := m))^[2 * m]) (sigmaVec 0 (-1)) =
      longE ((⟨0, by omega⟩ : Fin (m - 1)), (⟨0, by omega⟩ : Fin (m - 1))) := by
  rw [normalizedG0Vec_last_zero_initial hm hh2]
  ext i
  fin_cases i <;> simp [longE, longU, longV, EVec, Nat.cast_add]

theorem normalizedG0Vec_long_prefix {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (n : Nat) :
    let hm1 : 0 < m - 1 := by omega
    ((normalizedG0Vec (m := m))^[longPrefixTime m hm1 n]) (longE (longStart m hm1)) =
      match longIdxAfter m hm1 n with
      | some I => longE I
      | none => sigmaVec 1 0 := by
  have hm1 : 0 < m - 1 := by omega
  change
    ((normalizedG0Vec (m := m))^[longPrefixTime m hm1 n]) (longE (longStart m hm1)) =
      match longIdxAfter m hm1 n with
      | some I => longE I
      | none => sigmaVec 1 0
  induction n with
  | zero =>
      simp [longPrefixTime, longIdxAfter, longStart]
  | succ n ih =>
      dsimp [longPrefixTime, longIdxAfter]
      cases hafter : longIdxAfter m hm1 n with
      | none =>
          rw [hafter] at ih
          simpa [hafter] using ih
      | some I =>
          rw [hafter] at ih
          simp [hafter]
          rw [Function.iterate_add_apply]
          rw [ih]
          exact normalizedG0Vec_longE_step hm hh2 I

theorem normalizedG0Vec_long_prefix_segment_p5_no_earlier {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h)
    (n r : Nat) (I : LongIdx m) :
    let hm1 : 0 < m - 1 := by omega
    longIdxAfter m hm1 n = some I ->
    0 < r -> r < longStepTime m I ->
      p5 (((normalizedG0Vec (m := m))^[longPrefixTime m hm1 n + r])
        (longE (longStart m hm1))) ≠ 2 := by
  intro hm1 hafter hrpos hrlt
  have hprefix := normalizedG0Vec_long_prefix (m := m) (h := h) hm hh2 n
  change
    p5 (((normalizedG0Vec (m := m))^[longPrefixTime m hm1 n + r])
      (longE (longStart m hm1))) ≠ 2
  rw [Nat.add_comm]
  rw [Function.iterate_add_apply]
  have hprefixI :
      ((normalizedG0Vec (m := m))^[longPrefixTime m hm1 n]) (longE (longStart m hm1)) =
        longE I := by
    simpa [hafter] using hprefix
  rw [hprefixI]
  exact normalizedG0Vec_longE_step_p5_no_earlier hm hh2 I r hrpos hrlt

theorem normalizedG0Vec_long_prefix_boundary_p5_no_earlier {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h)
    (n : Nat) (I : LongIdx m) :
    let hm1 : 0 < m - 1 := by omega
    longIdxAfter m hm1 n = some I ->
      p5 (((normalizedG0Vec (m := m))^[longPrefixTime m hm1 n])
        (longE (longStart m hm1))) ≠ 2 := by
  intro hm1 hafter
  have hm5 : 5 <= m := by omega
  have hprefix := normalizedG0Vec_long_prefix (m := m) (h := h) hm hh2 n
  change
    p5 (((normalizedG0Vec (m := m))^[longPrefixTime m hm1 n])
      (longE (longStart m hm1))) ≠ 2
  have hprefixI :
      ((normalizedG0Vec (m := m))^[longPrefixTime m hm1 n]) (longE (longStart m hm1)) =
        longE I := by
    simpa [hafter] using hprefix
  rw [hprefixI]
  exact p5_longE_ne_two hm5 I

theorem normalizedG0Vec_long_prefix_p5_no_earlier {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (n : Nat) :
    let hm1 : 0 < m - 1 := by omega
    forall k : Nat, 0 < k -> k < longPrefixTime m hm1 n ->
      p5 (((normalizedG0Vec (m := m))^[k]) (longE (longStart m hm1))) ≠ 2 := by
  have hm1 : 0 < m - 1 := by omega
  change forall k : Nat, 0 < k -> k < longPrefixTime m hm1 n ->
      p5 (((normalizedG0Vec (m := m))^[k]) (longE (longStart m hm1))) ≠ 2
  induction n with
  | zero =>
      intro k _ hklt
      simp [longPrefixTime] at hklt
  | succ n ih =>
      intro k hkpos hklt
      cases hafter : longIdxAfter m hm1 n with
      | none =>
          simp [longPrefixTime, hafter] at hklt
          exact ih k hkpos hklt
      | some I =>
          simp [longPrefixTime, hafter] at hklt
          let p := longPrefixTime m hm1 n
          let step := longStepTime m I
          by_cases hkp : k < p
          · exact ih k hkpos hkp
          · by_cases hkeq : k = p
            · subst k
              exact normalizedG0Vec_long_prefix_boundary_p5_no_earlier hm hh2 n I hafter
            · let r := k - p
              have hrpos : 0 < r := by
                dsimp [r, p]
                omega
              have hrlt : r < step := by
                dsimp [r, p, step]
                omega
              have hk_eq : k = p + r := by
                dsimp [r, p]
                omega
              rw [hk_eq]
              exact normalizedG0Vec_long_prefix_segment_p5_no_earlier
                hm hh2 n r I hafter hrpos hrlt

theorem normalizedG0Vec_last_zero_long_prefix_end {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    let hm1 : 0 < m - 1 := by omega
    ((normalizedG0Vec (m := m))^[
        2 * m + longPrefixTime m hm1 ((m - 1) * (m - 1))])
      (sigmaVec 0 (-1)) =
      sigmaVec 1 0 := by
  have hm1 : 0 < m - 1 := by omega
  change
    ((normalizedG0Vec (m := m))^[
        2 * m + longPrefixTime m hm1 ((m - 1) * (m - 1))])
      (sigmaVec 0 (-1)) =
      sigmaVec 1 0
  rw [Nat.add_comm]
  rw [Function.iterate_add_apply]
  rw [normalizedG0Vec_last_zero_initial_longE hm hh2]
  have hprefix := normalizedG0Vec_long_prefix (m := m) (h := h) hm hh2
    ((m - 1) * (m - 1))
  change
    ((normalizedG0Vec (m := m))^[longPrefixTime m hm1 ((m - 1) * (m - 1))])
      (longE (longStart m hm1)) =
    sigmaVec 1 0
  simpa [longIdxAfter_end (m := m) hm1] using hprefix

theorem normalizedG0Vec_first_return_sigma_last_zero {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    ((normalizedG0Vec (m := m))^[returnTimeSigma hm hh2 (lastZeroSigmaParam hm hh2)])
        (sigmaVec 0 (-1)) =
      sigmaVec
        (nextSigma hm hh2 (lastZeroSigmaParam hm hh2)).1.1
        (nextSigma hm hh2 (lastZeroSigmaParam hm hh2)).1.2 := by
  rw [returnTimeSigma_last_zero hm hh2]
  rw [nextSigma_last_zero hm hh2]
  have hm5 : 5 <= m := by omega
  have hm1 : 0 < m - 1 := by omega
  have htime := longPrefixTime_end (m := m) hm1 hm5
  rw [← last_zero_total_time_eq (m := m) hm5]
  rw [← htime]
  exact normalizedG0Vec_last_zero_long_prefix_end hm hh2

theorem sum5_smul (m : Nat) (a : ZMod m) (w : Vec5 m) :
    sum5 m (a • w) = a * sum5 m w := by
  simp [sum5, Finset.mul_sum]

theorem root5_normalizedG0Drift (m : Nat) : Root5 m (normalizedG0Drift m) := by
  unfold normalizedG0Drift Root5
  rw [sum5_add, sum5_smul, sum5_q5, sum5_q5]
  simp

theorem root5_normalizedGcDrift (m : Nat) (c : Color) :
    Root5 m (normalizedGcDrift m c) := by
  unfold normalizedGcDrift
  apply root5_add_root
  · apply root5_add_root
    · unfold Root5
      rw [sum5_smul, sum5_q5]
      simp
    · exact root5_q5_vec m (fin5AddNat c 3)
  · exact root5_q5_vec m (fin5AddNat c 4)

theorem root5_normalizedG0Vec {m : Nat} {w : Vec5 m} (hw : Root5 m w) :
    Root5 m (normalizedG0Vec w) := by
  unfold normalizedG0Vec
  exact root5_add_q5 (root5_add_root hw (root5_normalizedG0Drift m)) (p5 w)

theorem root5_normalizedG0Vec_iter {m : Nat} {w : Vec5 m}
    (hw : Root5 m w) (n : Nat) :
    Root5 m (((normalizedG0Vec (m := m))^[n]) w) := by
  induction n with
  | zero => simpa using hw
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact root5_normalizedG0Vec ih

theorem normalizedG0Vec_last_zero_initial_p5_no_earlier {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    forall k : Nat, 0 < k -> k < 2 * m ->
      p5 (((normalizedG0Vec (m := m))^[k]) (sigmaVec 0 (-1))) ≠ 2 := by
  intro k hkpos hklt
  by_cases hkm : k <= m
  · let j := k - 1
    have hj : j <= m - 1 := by
      dsimp [j]
      omega
    have hk_eq : k = 1 + j := by
      dsimp [j]
      omega
    have hstate :
        ((normalizedG0Vec (m := m))^[k]) (sigmaVec 0 (-1)) =
        ![
          (-3 : ZMod m) - (3 : ZMod m) * (j : ZMod m),
          0,
          0,
          1 + (j : ZMod m),
          2 + (j : ZMod m) * (2 : ZMod m)
        ] := by
      rw [hk_eq]
      exact normalizedG0Vec_last_zero_initial_phase1 (m := m) (h := h)
        (j := j) hm hh2 hj
    have hwroot :
        Root5 m (((normalizedG0Vec (m := m))^[k]) (sigmaVec 0 (-1))) := by
      exact root5_normalizedG0Vec_iter (root5_sigmaVec 0 (-1)) k
    by_cases hjlast : j = m - 1
    · have h4zero :
          (((normalizedG0Vec (m := m))^[k]) (sigmaVec 0 (-1))) 4 = 0 := by
        rw [hstate]
        simp [hjlast]
        rw [zmod_nat_pred_self_eq_neg_one (m := m)]
        ring
      exact p5_ne_two_of_root_guard hwroot (Or.inr (Or.inr h4zero))
    · have hjlt : j < m - 1 := by omega
      have h3ne :
          (((normalizedG0Vec (m := m))^[k]) (sigmaVec 0 (-1))) 3 ≠ 0 := by
        rw [hstate]
        simp
        exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := j) hjlt
      exact p5_ne_two_of_root_guard hwroot (Or.inr (Or.inl h3ne))
  · let j := k - (m + 1)
    have hj : j <= m - 1 := by
      dsimp [j]
      omega
    have hjlt : j < m - 1 := by
      dsimp [j]
      omega
    have hk_eq : k = m + 1 + j := by
      dsimp [j]
      omega
    have hstate :
        ((normalizedG0Vec (m := m))^[k]) (sigmaVec 0 (-1)) =
        ![
          (-2 : ZMod m) - (3 : ZMod m) * (j : ZMod m),
          0,
          0,
          1 + (j : ZMod m),
          1 + (j : ZMod m) * (2 : ZMod m)
        ] := by
      rw [hk_eq]
      exact normalizedG0Vec_last_zero_initial_phase2 (m := m) (h := h)
        (j := j) hm hh2 hj
    have hwroot :
        Root5 m (((normalizedG0Vec (m := m))^[k]) (sigmaVec 0 (-1))) := by
      exact root5_normalizedG0Vec_iter (root5_sigmaVec 0 (-1)) k
    have h3ne :
        (((normalizedG0Vec (m := m))^[k]) (sigmaVec 0 (-1))) 3 ≠ 0 := by
      rw [hstate]
      simp
      exact zmod_one_add_nat_ne_zero_before_mod (m := m) (k := j) hjlt
    exact p5_ne_two_of_root_guard hwroot (Or.inr (Or.inl h3ne))

theorem normalizedG0Vec_last_zero_p5_no_earlier {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    forall k : Nat, 0 < k -> k < returnTimeSigma hm hh2 (lastZeroSigmaParam hm hh2) ->
      p5 (((normalizedG0Vec (m := m))^[k]) (sigmaVec 0 (-1))) ≠ 2 := by
  have hm5 : 5 <= m := by omega
  have hm1 : 0 < m - 1 := by omega
  intro k hkpos hklt
  rw [returnTimeSigma_last_zero hm hh2] at hklt
  rw [← last_zero_total_time_eq (m := m) hm5] at hklt
  rw [← longPrefixTime_end (m := m) hm1 hm5] at hklt
  by_cases hkinit : k < 2 * m
  · exact normalizedG0Vec_last_zero_initial_p5_no_earlier hm hh2 k hkpos hkinit
  · let t := k - 2 * m
    have htlt : t < longPrefixTime m hm1 ((m - 1) * (m - 1)) := by
      dsimp [t]
      omega
    by_cases ht0 : t = 0
    · have hk_eq : k = 2 * m := by
        dsimp [t] at ht0
        omega
      rw [hk_eq]
      have hstate :
          ((normalizedG0Vec (m := m))^[2 * m]) (sigmaVec 0 (-1)) =
            longE (longStart m hm1) := by
        simpa [longStart] using normalizedG0Vec_last_zero_initial_longE hm hh2
      rw [hstate]
      exact p5_longE_ne_two hm5 (longStart m hm1)
    · have htpos : 0 < t := by omega
      have hk_eq : k = 2 * m + t := by
        dsimp [t]
        omega
      rw [hk_eq]
      rw [Nat.add_comm]
      rw [Function.iterate_add_apply]
      have hstate :
          ((normalizedG0Vec (m := m))^[2 * m]) (sigmaVec 0 (-1)) =
            longE (longStart m hm1) := by
        simpa [longStart] using normalizedG0Vec_last_zero_initial_longE hm hh2
      rw [hstate]
      exact normalizedG0Vec_long_prefix_p5_no_earlier hm hh2
        ((m - 1) * (m - 1)) t htpos htlt

def normalizedG0 {m : Nat} (w : ARoot5 m) : ARoot5 m :=
  ⟨normalizedG0Vec w.1, root5_normalizedG0Vec w.2⟩

def normalizedGc {m : Nat} (c : Color) (w : ARoot5 m) : ARoot5 m :=
  rootTranslate (normalizedGcDrift m c) (root5_normalizedGcDrift m c) (colorPc c w)

theorem normalizedG0_iter_val {m : Nat} (n : Nat) (w : ARoot5 m) :
    (((normalizedG0 (m := m))^[n]) w).1 =
      ((normalizedG0Vec (m := m))^[n]) w.1 := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      simp [normalizedG0, ih]

theorem normalizedG0_first_return_sigma_nonlast {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a b : ZMod m}
    (hab : a + b ≠ 0) (hB : b + 1 ≠ 0) :
    ((normalizedG0 (m := m))^[returnTimeSigma hm hh2 ⟨(a, b), hab⟩])
        (sigmaBase ⟨(a, b), hab⟩) =
      sigmaBase (nextSigma hm hh2 ⟨(a, b), hab⟩) := by
  apply Subtype.ext
  rw [normalizedG0_iter_val]
  dsimp [sigmaBase, sigmaPoint]
  exact normalizedG0Vec_first_return_sigma_nonlast hm hh2 hab hB

theorem normalizedG0_first_return_sigma_last_nonzero {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a : ZMod m}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    ((normalizedG0 (m := m))^[returnTimeSigma hm hh2 (lastSigmaParam a ha1)])
        (sigmaBase (lastSigmaParam a ha1)) =
      sigmaBase (nextSigma hm hh2 (lastSigmaParam a ha1)) := by
  apply Subtype.ext
  rw [normalizedG0_iter_val]
  dsimp [sigmaBase, sigmaPoint, lastSigmaParam]
  exact normalizedG0Vec_first_return_sigma_last_nonzero hm hh2 ha0 ha1

theorem normalizedG0_p5_no_earlier_nonlast {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a b : ZMod m}
    (hab : a + b ≠ 0) (hB : b + 1 ≠ 0) :
    forall k : Nat, 0 < k -> k < returnTimeSigma hm hh2 ⟨(a, b), hab⟩ ->
      p5 ((((normalizedG0 (m := m))^[k]) (sigmaBase ⟨(a, b), hab⟩)).1) ≠ 2 := by
  intro k hkpos hklt
  rw [normalizedG0_iter_val]
  dsimp [sigmaBase, sigmaPoint]
  exact normalizedG0Vec_first_return_sigma_nonlast_p5_no_earlier
    hm hh2 hab hB k hkpos hklt

theorem normalizedG0_p5_no_earlier_last_nonzero {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) {a : ZMod m}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    forall k : Nat, 0 < k -> k < returnTimeSigma hm hh2 (lastSigmaParam a ha1) ->
      p5 ((((normalizedG0 (m := m))^[k]) (sigmaBase (lastSigmaParam a ha1))).1) ≠ 2 := by
  intro k hkpos hklt
  rw [normalizedG0_iter_val]
  dsimp [sigmaBase, sigmaPoint, lastSigmaParam]
  apply normalizedG0Vec_last_nonzero_p5_no_earlier hm hh2 ha0 ha1 k hkpos
  rw [returnTimeSigma_last_nonzero hm hh2 ha0 ha1] at hklt
  exact hklt

theorem normalizedG0_p5_no_earlier_last_zero_initial {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    forall k : Nat, 0 < k -> k < 2 * m ->
      p5 ((((normalizedG0 (m := m))^[k]) (sigmaBase (lastZeroSigmaParam hm hh2))).1) ≠ 2 := by
  intro k hkpos hklt
  rw [normalizedG0_iter_val]
  dsimp [sigmaBase, sigmaPoint, lastZeroSigmaParam, lastSigmaParam]
  exact normalizedG0Vec_last_zero_initial_p5_no_earlier hm hh2 k hkpos hklt

theorem normalizedG0_p5_no_earlier_last_zero {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    forall k : Nat, 0 < k -> k < returnTimeSigma hm hh2 (lastZeroSigmaParam hm hh2) ->
      p5 ((((normalizedG0 (m := m))^[k]) (sigmaBase (lastZeroSigmaParam hm hh2))).1) ≠ 2 := by
  intro k hkpos hklt
  rw [normalizedG0_iter_val]
  dsimp [sigmaBase, sigmaPoint, lastZeroSigmaParam, lastSigmaParam]
  exact normalizedG0Vec_last_zero_p5_no_earlier hm hh2 k hkpos hklt

theorem normalizedG0_p5_no_earlier_sigma {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    forall s : SigmaParam m, forall k : Nat,
      0 < k -> k < returnTimeSigma hm hh2 s ->
        p5 ((((normalizedG0 (m := m))^[k]) (sigmaBase s)).1) ≠ 2 := by
  intro s k hkpos hklt
  rcases s with ⟨⟨a, b⟩, hab⟩
  by_cases hB : b + 1 = 0
  · have hb : b = -1 := by
      linear_combination hB
    by_cases ha0 : a = 0
    · have hs :
          (⟨(a, b), hab⟩ : SigmaParam m) = lastZeroSigmaParam hm hh2 := by
        apply Subtype.ext
        ext <;> simp [lastZeroSigmaParam, lastSigmaParam, ha0, hb]
      rw [hs] at hklt
      rw [hs]
      exact normalizedG0_p5_no_earlier_last_zero hm hh2 k hkpos hklt
    · have ha1 : a ≠ 1 := by
        intro h1
        apply hab
        simpa [h1, hb]
      have hs : (⟨(a, b), hab⟩ : SigmaParam m) = lastSigmaParam a ha1 := by
        apply Subtype.ext
        ext <;> simp [lastSigmaParam, hb]
      rw [hs] at hklt
      rw [hs]
      exact normalizedG0_p5_no_earlier_last_nonzero hm hh2 ha0 ha1 k hkpos hklt
  · exact normalizedG0_p5_no_earlier_nonlast hm hh2 hab hB k hkpos hklt

theorem normalizedG0_first_return_sigma_last_zero {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    ((normalizedG0 (m := m))^[returnTimeSigma hm hh2 (lastZeroSigmaParam hm hh2)])
        (sigmaBase (lastZeroSigmaParam hm hh2)) =
      sigmaBase (nextSigma hm hh2 (lastZeroSigmaParam hm hh2)) := by
  apply Subtype.ext
  rw [normalizedG0_iter_val]
  dsimp [sigmaBase, sigmaPoint, lastZeroSigmaParam, lastSigmaParam]
  exact normalizedG0Vec_first_return_sigma_last_zero hm hh2

theorem normalizedG0_first_return_sigma {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    forall s : SigmaParam m,
      ((normalizedG0 (m := m))^[returnTimeSigma hm hh2 s]) (sigmaBase s) =
        sigmaBase (nextSigma hm hh2 s) := by
  intro s
  rcases s with ⟨⟨a, b⟩, hab⟩
  by_cases hB : b + 1 = 0
  · have hb : b = -1 := by
      linear_combination hB
    by_cases ha0 : a = 0
    · have hs :
          (⟨(a, b), hab⟩ : SigmaParam m) = lastZeroSigmaParam hm hh2 := by
        apply Subtype.ext
        ext <;> simp [lastZeroSigmaParam, lastSigmaParam, ha0, hb]
      rw [hs]
      exact normalizedG0_first_return_sigma_last_zero hm hh2
    · have ha1 : a ≠ 1 := by
        intro h1
        apply hab
        simpa [h1, hb]
      have hs : (⟨(a, b), hab⟩ : SigmaParam m) = lastSigmaParam a ha1 := by
        apply Subtype.ext
        ext <;> simp [lastSigmaParam, hb]
      rw [hs]
      exact normalizedG0_first_return_sigma_last_nonzero hm hh2 ha0 ha1
  · exact normalizedG0_first_return_sigma_nonlast hm hh2 hab hB

theorem normalizedG0_eq_translate_colorZeroP {m : Nat} (w : ARoot5 m) :
    normalizedG0 w =
      rootTranslate (normalizedG0Drift m) (root5_normalizedG0Drift m) (colorZeroP w) := by
  apply Subtype.ext
  simp [normalizedG0, normalizedG0Vec, rootTranslate, colorZeroP,
    add_comm, add_left_comm]

theorem colorReturn_ge5_zero_semiconj_add5 (n : Nat) :
    forall w : ARoot5 (n + 5),
      rootTranslate (-q5 (n + 5) 0) (root5_neg_q5_vec (n + 5) 0)
        (normalizedG0 (m := n + 5) w) =
      colorReturn (ge5Schedule (n + 5)) 0
        (rootTranslate (-q5 (n + 5) 0) (root5_neg_q5_vec (n + 5) 0) w) := by
  intro w
  unfold colorReturn
  change rootTranslate (-q5 (n + 5) 0) (root5_neg_q5_vec (n + 5) 0)
        (normalizedG0 (m := n + 5) w) =
      List.foldl (fun x t => layerMap (ge5Schedule (n + 5)) t 0 x)
        (rootTranslate (-q5 (n + 5) 0) (root5_neg_q5_vec (n + 5) 0) w)
        (List.finRange ((n + 4) + 1))
  rw [List.finRange_succ, List.foldl_cons]
  have h0 : layerMap (ge5Schedule (n + 5)) (0 : Fin ((n + 4) + 1)) 0
      (rootTranslate (-q5 (n + 5) 0) (root5_neg_q5_vec (n + 5) 0) w) = w := by
    rw [layerMap_ge5_color0_regular]
    · apply Subtype.ext
      simp [rootTranslate]
    · simp
    · simp
    · simp
  rw [h0]
  rw [List.foldl_map]
  change rootTranslate (-q5 (n + 5) 0) (root5_neg_q5_vec (n + 5) 0)
        (normalizedG0 (m := n + 5) w) =
      List.foldl (fun x t => layerMap (ge5Schedule (n + 5)) (Fin.succ t) 0 x)
        w (List.finRange ((n + 3) + 1))
  rw [List.finRange_succ, List.foldl_cons]
  have h1 : layerMap (ge5Schedule (n + 5)) (Fin.succ (0 : Fin (n + 4))) 0 w =
      colorZeroP w := by
    apply Subtype.ext
    simp [layerMap, colorZeroP, ge5Schedule, ge5Dir, p5]
  rw [h1]
  rw [List.foldl_map]
  change rootTranslate (-q5 (n + 5) 0) (root5_neg_q5_vec (n + 5) 0)
        (normalizedG0 (m := n + 5) w) =
      List.foldl (fun x t => layerMap (ge5Schedule (n + 5)) (Fin.succ (Fin.succ t)) 0 x)
        (colorZeroP w) (List.finRange ((n + 2) + 1))
  rw [List.finRange_succ, List.foldl_cons]
  have h2 : layerMap (ge5Schedule (n + 5))
        (Fin.succ (Fin.succ (0 : Fin (n + 3)))) 0 (colorZeroP w) =
      rootTranslate (q5 (n + 5) 3) (root5_q5_vec (n + 5) 3) (colorZeroP w) := by
    exact layerMap_ge5_color0_two _ (by simp) _
  rw [h2]
  rw [List.foldl_map]
  change rootTranslate (-q5 (n + 5) 0) (root5_neg_q5_vec (n + 5) 0)
        (normalizedG0 (m := n + 5) w) =
      List.foldl
        (fun x t => layerMap (ge5Schedule (n + 5)) (Fin.succ (Fin.succ (Fin.succ t))) 0 x)
        (rootTranslate (q5 (n + 5) 3) (root5_q5_vec (n + 5) 3) (colorZeroP w))
        (List.finRange ((n + 1) + 1))
  rw [List.finRange_succ, List.foldl_cons]
  have h3 : layerMap (ge5Schedule (n + 5))
        (Fin.succ (Fin.succ (Fin.succ (0 : Fin (n + 2))))) 0
        (rootTranslate (q5 (n + 5) 3) (root5_q5_vec (n + 5) 3) (colorZeroP w)) =
      rootTranslate (q5 (n + 5) 4) (root5_q5_vec (n + 5) 4)
        (rootTranslate (q5 (n + 5) 3) (root5_q5_vec (n + 5) 3) (colorZeroP w)) := by
    exact layerMap_ge5_color0_three _ (by simp) _
  rw [h3]
  rw [List.foldl_map]
  change rootTranslate (-q5 (n + 5) 0) (root5_neg_q5_vec (n + 5) 0)
        (normalizedG0 (m := n + 5) w) =
      List.foldl (fun x t => layerMap (ge5Schedule (n + 5)) (finSucc4 t) 0 x)
        (rootTranslate (q5 (n + 5) 4) (root5_q5_vec (n + 5) 4)
          (rootTranslate (q5 (n + 5) 3) (root5_q5_vec (n + 5) 3) (colorZeroP w)))
        (List.finRange (n + 1))
  rw [← List.foldl_map (f := finSucc4)
    (g := fun x t => layerMap (ge5Schedule (n + 5)) t 0 x) (l := List.finRange (n + 1))]
  rw [fold_ge5_color0_regular]
  · simp [List.length_map, List.length_finRange]
    rw [normalizedG0_eq_translate_colorZeroP]
    apply Subtype.ext
    ext i
    have hv := congrFun (ge5_zero_tail_vector n) i
    simp [rootTranslate] at hv ⊢
    abel_nf at hv ⊢
    linear_combination -hv
  · intro t ht
    rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
    simp [finSucc4]

theorem colorReturn_ge5_semiconj_add5 (n : Nat) (c : Color) :
    forall w : ARoot5 (n + 5),
      rootTranslate (-q5 (n + 5) c) (root5_neg_q5_vec (n + 5) c)
        (rootRotate c (normalizedG0 (m := n + 5) w)) =
      colorReturn (ge5Schedule (n + 5)) c
        (rootTranslate (-q5 (n + 5) c) (root5_neg_q5_vec (n + 5) c)
          (rootRotate c w)) := by
  intro w
  unfold colorReturn
  change rootTranslate (-q5 (n + 5) c) (root5_neg_q5_vec (n + 5) c)
        (rootRotate c (normalizedG0 (m := n + 5) w)) =
      List.foldl (fun x t => layerMap (ge5Schedule (n + 5)) t c x)
        (rootTranslate (-q5 (n + 5) c) (root5_neg_q5_vec (n + 5) c) (rootRotate c w))
        (List.finRange ((n + 4) + 1))
  rw [List.finRange_succ, List.foldl_cons]
  have h0 : layerMap (ge5Schedule (n + 5)) (0 : Fin ((n + 4) + 1)) c
      (rootTranslate (-q5 (n + 5) c) (root5_neg_q5_vec (n + 5) c) (rootRotate c w)) =
      rootRotate c w := by
    rw [layerMap_ge5_regular]
    · apply Subtype.ext
      simp [rootTranslate]
    · simp
    · simp
    · simp
  rw [h0]
  rw [List.foldl_map]
  change rootTranslate (-q5 (n + 5) c) (root5_neg_q5_vec (n + 5) c)
        (rootRotate c (normalizedG0 (m := n + 5) w)) =
      List.foldl (fun x t => layerMap (ge5Schedule (n + 5)) (Fin.succ t) c x)
        (rootRotate c w) (List.finRange ((n + 3) + 1))
  rw [List.finRange_succ, List.foldl_cons]
  have h1 : layerMap (ge5Schedule (n + 5)) (Fin.succ (0 : Fin (n + 4))) c
      (rootRotate c w) =
      colorPc c (rootRotate c w) := by
    apply Subtype.ext
    simp [layerMap, colorPc, ge5Schedule, ge5Dir, pc5]
  rw [h1]
  rw [List.foldl_map]
  change rootTranslate (-q5 (n + 5) c) (root5_neg_q5_vec (n + 5) c)
        (rootRotate c (normalizedG0 (m := n + 5) w)) =
      List.foldl (fun x t => layerMap (ge5Schedule (n + 5)) (Fin.succ (Fin.succ t)) c x)
        (colorPc c (rootRotate c w)) (List.finRange ((n + 2) + 1))
  rw [List.finRange_succ, List.foldl_cons]
  have h2 : layerMap (ge5Schedule (n + 5))
        (Fin.succ (Fin.succ (0 : Fin (n + 3)))) c (colorPc c (rootRotate c w)) =
      rootTranslate (q5 (n + 5) (fin5AddNat c 3))
        (root5_q5_vec (n + 5) (fin5AddNat c 3)) (colorPc c (rootRotate c w)) := by
    exact layerMap_ge5_two _ c (by simp) _
  rw [h2]
  rw [List.foldl_map]
  change rootTranslate (-q5 (n + 5) c) (root5_neg_q5_vec (n + 5) c)
        (rootRotate c (normalizedG0 (m := n + 5) w)) =
      List.foldl
        (fun x t => layerMap (ge5Schedule (n + 5)) (Fin.succ (Fin.succ (Fin.succ t))) c x)
        (rootTranslate (q5 (n + 5) (fin5AddNat c 3))
          (root5_q5_vec (n + 5) (fin5AddNat c 3)) (colorPc c (rootRotate c w)))
        (List.finRange ((n + 1) + 1))
  rw [List.finRange_succ, List.foldl_cons]
  have h3 : layerMap (ge5Schedule (n + 5))
        (Fin.succ (Fin.succ (Fin.succ (0 : Fin (n + 2))))) c
        (rootTranslate (q5 (n + 5) (fin5AddNat c 3))
          (root5_q5_vec (n + 5) (fin5AddNat c 3)) (colorPc c (rootRotate c w))) =
      rootTranslate (q5 (n + 5) (fin5AddNat c 4))
        (root5_q5_vec (n + 5) (fin5AddNat c 4))
        (rootTranslate (q5 (n + 5) (fin5AddNat c 3))
          (root5_q5_vec (n + 5) (fin5AddNat c 3)) (colorPc c (rootRotate c w))) := by
    exact layerMap_ge5_three _ c (by simp) _
  rw [h3]
  rw [List.foldl_map]
  change rootTranslate (-q5 (n + 5) c) (root5_neg_q5_vec (n + 5) c)
        (rootRotate c (normalizedG0 (m := n + 5) w)) =
      List.foldl (fun x t => layerMap (ge5Schedule (n + 5)) (finSucc4 t) c x)
        (rootTranslate (q5 (n + 5) (fin5AddNat c 4))
          (root5_q5_vec (n + 5) (fin5AddNat c 4))
          (rootTranslate (q5 (n + 5) (fin5AddNat c 3))
            (root5_q5_vec (n + 5) (fin5AddNat c 3)) (colorPc c (rootRotate c w))))
        (List.finRange (n + 1))
  rw [← List.foldl_map (f := finSucc4)
    (g := fun x t => layerMap (ge5Schedule (n + 5)) t c x) (l := List.finRange (n + 1))]
  rw [fold_ge5_regular]
  · simp [List.length_map, List.length_finRange]
    apply Subtype.ext
    ext i
    have hp : pc5 c (rotVec c w.1) = fin5AddNat (p5 w.1) c.val := pc5_rotVec c w.1
    have hv := congrFun (ge5_color_tail_vector n c (p5 w.1)) i
    simp [normalizedG0, normalizedG0Vec, rootTranslate, rootRotate, colorPc, rotVec, hp] at hv ⊢
    abel_nf at hv ⊢
    linear_combination hv
  · intro t ht
    rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
    simp [finSucc4]

theorem normalizedG0_bijective {m : Nat} [NeZero m] (hm : 5 <= m) :
    Function.Bijective (normalizedG0 (m := m)) := by
  rw [show normalizedG0 (m := m) =
      (rootTranslate (normalizedG0Drift m) (root5_normalizedG0Drift m)) ∘ colorZeroP by
    funext w
    exact normalizedG0_eq_translate_colorZeroP w]
  exact Function.Bijective.comp
    (rootTranslate_bijective (normalizedG0Drift m) (root5_normalizedG0Drift m))
    (colorZeroP_bijective hm)

theorem normalizedG0_single_cycle_of_return_cover {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h)
    (hcover : forall x : ARoot5 m, exists s : SigmaParam m, exists k : Nat,
      k < returnTimeSigma hm hh2 s ∧
        ((normalizedG0 (m := m))^[k]) (sigmaBase s) = x) :
    IsSingleCycleMap (normalizedG0 (m := m)) := by
  have hm5 : 5 <= m := by omega
  exact single_cycle_of_return_cover
    (f := normalizedG0 (m := m))
    (base := sigmaBase (m := m))
    (next := nextSigma hm hh2)
    (time := returnTimeSigma hm hh2)
    (normalizedG0_bijective hm5)
    (normalizedG0_first_return_sigma hm hh2)
    hcover
    (nextSigma_single_cycle hm hh2)

theorem normalizedG0_single_cycle_of_first_return_sum {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h)
    (hfirst : forall s : SigmaParam m, forall k : Nat,
      0 < k -> k < returnTimeSigma hm hh2 s ->
        ¬ exists t : SigmaParam m,
          ((normalizedG0 (m := m))^[k]) (sigmaBase s) = sigmaBase t)
    (hsum :
      (Finset.univ.sum fun s : SigmaParam m => returnTimeSigma hm hh2 s) =
        Fintype.card (ARoot5 m)) :
    IsSingleCycleMap (normalizedG0 (m := m)) := by
  have hm5 : 5 <= m := by omega
  exact single_cycle_of_first_return_sum
    (f := normalizedG0 (m := m))
    (base := sigmaBase (m := m))
    (next := nextSigma hm hh2)
    (time := returnTimeSigma hm hh2)
    (normalizedG0_bijective hm5)
    sigmaBase_injective
    (normalizedG0_first_return_sigma hm hh2)
    hfirst
    (nextSigma_single_cycle hm hh2)
    hsum

theorem normalizedG0_single_cycle_of_p5_first_return_sum {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h)
    (hpfirst : forall s : SigmaParam m, forall k : Nat,
      0 < k -> k < returnTimeSigma hm hh2 s ->
        p5 ((((normalizedG0 (m := m))^[k]) (sigmaBase s)).1) ≠ 2)
    (hsum :
      (Finset.univ.sum fun s : SigmaParam m => returnTimeSigma hm hh2 s) =
        Fintype.card (ARoot5 m)) :
    IsSingleCycleMap (normalizedG0 (m := m)) := by
  apply normalizedG0_single_cycle_of_first_return_sum hm hh2
  · intro s k hkpos hklt
    exact not_exists_sigmaBase_of_p5_ne_two (hpfirst s k hkpos hklt)
  · exact hsum

theorem normalizedG0_single_cycle_of_p5_first_return_sum_m4 {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h)
    (hpfirst : forall s : SigmaParam m, forall k : Nat,
      0 < k -> k < returnTimeSigma hm hh2 s ->
        p5 ((((normalizedG0 (m := m))^[k]) (sigmaBase s)).1) ≠ 2)
    (hsum :
      (Finset.univ.sum fun s : SigmaParam m => returnTimeSigma hm hh2 s) =
        m ^ 4) :
    IsSingleCycleMap (normalizedG0 (m := m)) := by
  apply normalizedG0_single_cycle_of_p5_first_return_sum hm hh2 hpfirst
  rw [card_ARoot5]
  exact hsum

theorem normalizedG0_single_cycle_of_p5_first_return {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h)
    (hpfirst : forall s : SigmaParam m, forall k : Nat,
      0 < k -> k < returnTimeSigma hm hh2 s ->
        p5 ((((normalizedG0 (m := m))^[k]) (sigmaBase s)).1) ≠ 2) :
    IsSingleCycleMap (normalizedG0 (m := m)) := by
  exact normalizedG0_single_cycle_of_p5_first_return_sum_m4
    hm hh2 hpfirst (returnTimeSigma_sum_m4 hm hh2)

theorem normalizedG0_single_cycle {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    IsSingleCycleMap (normalizedG0 (m := m)) := by
  exact normalizedG0_single_cycle_of_p5_first_return hm hh2
    (normalizedG0_p5_no_earlier_sigma hm hh2)

theorem colorReturn_ge5_zero_single_cycle {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    IsSingleCycleMap (colorReturn (ge5Schedule m) 0) := by
  subst m
  let n : Nat := 2 * h - 4
  rw [show 2 * h + 1 = n + 5 by omega]
  exact single_cycle_of_bijective_semiconj
    (f := normalizedG0 (m := n + 5))
    (g := colorReturn (ge5Schedule (n + 5)) 0)
    (phi := rootTranslate (-q5 (n + 5) 0) (root5_neg_q5_vec (n + 5) 0))
    (rootTranslate_bijective (-q5 (n + 5) 0) (root5_neg_q5_vec (n + 5) 0))
    (colorReturn_ge5_zero_semiconj_add5 n)
    (normalizedG0_single_cycle (m := n + 5) (h := h) (by omega) hh2)

theorem colorReturn_ge5_single_cycle {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) (c : Color) :
    IsSingleCycleMap (colorReturn (ge5Schedule m) c) := by
  subst m
  let n : Nat := 2 * h - 4
  rw [show 2 * h + 1 = n + 5 by omega]
  exact single_cycle_of_bijective_semiconj
    (f := normalizedG0 (m := n + 5))
    (g := colorReturn (ge5Schedule (n + 5)) c)
    (phi := fun w : ARoot5 (n + 5) =>
      rootTranslate (-q5 (n + 5) c) (root5_neg_q5_vec (n + 5) c) (rootRotate c w))
    (Function.Bijective.comp
      (rootTranslate_bijective (-q5 (n + 5) c) (root5_neg_q5_vec (n + 5) c))
      (rootRotate_bijective c))
    (colorReturn_ge5_semiconj_add5 n c)
    (normalizedG0_single_cycle (m := n + 5) (h := h) (by omega) hh2)

theorem ge5Schedule_allColorHamiltonian {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    AllColorHamiltonian (ge5Schedule m) := by
  intro c
  exact colorReturn_ge5_single_cycle hm hh2 c

def m3ReturnQuad (c : Color) (x : Fin 4 -> ZMod 3) : Fin 4 -> ZMod 3 :=
  quadOfRoot (colorReturn m3Schedule c (rootOfQuad x))

def m3Rank (c : Color) (x : Fin 4 -> ZMod 3) : Fin 81 :=
  match c with
  | 0 =>
    match (x 0).val, (x 1).val, (x 2).val, (x 3).val with
    | 0, 0, 0, 0 => ⟨0, by decide⟩
    | 1, 0, 0, 1 => ⟨1, by decide⟩
    | 1, 0, 0, 2 => ⟨2, by decide⟩
    | 1, 0, 0, 0 => ⟨3, by decide⟩
    | 1, 1, 0, 1 => ⟨4, by decide⟩
    | 1, 1, 0, 0 => ⟨5, by decide⟩
    | 1, 2, 0, 1 => ⟨6, by decide⟩
    | 2, 2, 0, 2 => ⟨7, by decide⟩
    | 2, 2, 0, 1 => ⟨8, by decide⟩
    | 0, 2, 0, 2 => ⟨9, by decide⟩
    | 1, 2, 0, 0 => ⟨10, by decide⟩
    | 1, 2, 0, 2 => ⟨11, by decide⟩
    | 2, 2, 0, 0 => ⟨12, by decide⟩
    | 2, 0, 0, 1 => ⟨13, by decide⟩
    | 2, 0, 0, 2 => ⟨14, by decide⟩
    | 2, 0, 0, 0 => ⟨15, by decide⟩
    | 2, 1, 0, 1 => ⟨16, by decide⟩
    | 0, 1, 0, 2 => ⟨17, by decide⟩
    | 0, 1, 0, 1 => ⟨18, by decide⟩
    | 1, 1, 0, 2 => ⟨19, by decide⟩
    | 2, 1, 0, 0 => ⟨20, by decide⟩
    | 2, 1, 0, 2 => ⟨21, by decide⟩
    | 0, 1, 0, 0 => ⟨22, by decide⟩
    | 0, 1, 1, 1 => ⟨23, by decide⟩
    | 0, 2, 1, 2 => ⟨24, by decide⟩
    | 1, 2, 1, 0 => ⟨25, by decide⟩
    | 1, 2, 1, 1 => ⟨26, by decide⟩
    | 2, 2, 1, 2 => ⟨27, by decide⟩
    | 0, 2, 1, 0 => ⟨28, by decide⟩
    | 0, 0, 1, 1 => ⟨29, by decide⟩
    | 1, 0, 1, 2 => ⟨30, by decide⟩
    | 2, 0, 1, 0 => ⟨31, by decide⟩
    | 2, 0, 1, 1 => ⟨32, by decide⟩
    | 0, 0, 1, 2 => ⟨33, by decide⟩
    | 0, 1, 1, 0 => ⟨34, by decide⟩
    | 0, 1, 2, 1 => ⟨35, by decide⟩
    | 1, 1, 2, 2 => ⟨36, by decide⟩
    | 1, 2, 2, 0 => ⟨37, by decide⟩
    | 1, 2, 2, 1 => ⟨38, by decide⟩
    | 1, 0, 2, 2 => ⟨39, by decide⟩
    | 2, 0, 2, 0 => ⟨40, by decide⟩
    | 2, 0, 2, 1 => ⟨41, by decide⟩
    | 0, 0, 2, 2 => ⟨42, by decide⟩
    | 1, 0, 2, 0 => ⟨43, by decide⟩
    | 1, 0, 2, 1 => ⟨44, by decide⟩
    | 2, 0, 2, 2 => ⟨45, by decide⟩
    | 2, 1, 2, 0 => ⟨46, by decide⟩
    | 2, 1, 2, 1 => ⟨47, by decide⟩
    | 2, 2, 2, 2 => ⟨48, by decide⟩
    | 0, 2, 2, 0 => ⟨49, by decide⟩
    | 0, 2, 0, 1 => ⟨50, by decide⟩
    | 0, 2, 0, 0 => ⟨51, by decide⟩
    | 0, 2, 1, 1 => ⟨52, by decide⟩
    | 1, 2, 1, 2 => ⟨53, by decide⟩
    | 1, 0, 1, 0 => ⟨54, by decide⟩
    | 1, 0, 1, 1 => ⟨55, by decide⟩
    | 1, 1, 1, 2 => ⟨56, by decide⟩
    | 2, 1, 1, 0 => ⟨57, by decide⟩
    | 2, 1, 1, 1 => ⟨58, by decide⟩
    | 0, 1, 1, 2 => ⟨59, by decide⟩
    | 1, 1, 1, 0 => ⟨60, by decide⟩
    | 1, 1, 1, 1 => ⟨61, by decide⟩
    | 2, 1, 1, 2 => ⟨62, by decide⟩
    | 2, 2, 1, 0 => ⟨63, by decide⟩
    | 2, 2, 1, 1 => ⟨64, by decide⟩
    | 2, 0, 1, 2 => ⟨65, by decide⟩
    | 0, 0, 1, 0 => ⟨66, by decide⟩
    | 0, 0, 2, 1 => ⟨67, by decide⟩
    | 0, 1, 2, 2 => ⟨68, by decide⟩
    | 1, 1, 2, 0 => ⟨69, by decide⟩
    | 1, 1, 2, 1 => ⟨70, by decide⟩
    | 2, 1, 2, 2 => ⟨71, by decide⟩
    | 0, 1, 2, 0 => ⟨72, by decide⟩
    | 0, 2, 2, 1 => ⟨73, by decide⟩
    | 1, 2, 2, 2 => ⟨74, by decide⟩
    | 2, 2, 2, 0 => ⟨75, by decide⟩
    | 2, 2, 2, 1 => ⟨76, by decide⟩
    | 0, 2, 2, 2 => ⟨77, by decide⟩
    | 0, 0, 2, 0 => ⟨78, by decide⟩
    | 0, 0, 0, 1 => ⟨79, by decide⟩
    | 0, 0, 0, 2 => ⟨80, by decide⟩
    | _, _, _, _ => ⟨0, by decide⟩
  | 1 =>
    match (x 0).val, (x 1).val, (x 2).val, (x 3).val with
    | 0, 0, 0, 0 => ⟨0, by decide⟩
    | 2, 0, 0, 0 => ⟨1, by decide⟩
    | 0, 1, 0, 0 => ⟨2, by decide⟩
    | 2, 1, 0, 0 => ⟨3, by decide⟩
    | 1, 1, 0, 0 => ⟨4, by decide⟩
    | 2, 1, 1, 0 => ⟨5, by decide⟩
    | 0, 1, 1, 0 => ⟨6, by decide⟩
    | 1, 1, 2, 0 => ⟨7, by decide⟩
    | 2, 2, 2, 0 => ⟨8, by decide⟩
    | 0, 2, 2, 0 => ⟨9, by decide⟩
    | 1, 0, 2, 0 => ⟨10, by decide⟩
    | 2, 1, 2, 0 => ⟨11, by decide⟩
    | 0, 1, 2, 0 => ⟨12, by decide⟩
    | 1, 2, 2, 0 => ⟨13, by decide⟩
    | 2, 2, 0, 0 => ⟨14, by decide⟩
    | 1, 2, 0, 0 => ⟨15, by decide⟩
    | 0, 2, 0, 0 => ⟨16, by decide⟩
    | 1, 2, 1, 0 => ⟨17, by decide⟩
    | 2, 0, 1, 0 => ⟨18, by decide⟩
    | 0, 0, 1, 0 => ⟨19, by decide⟩
    | 1, 1, 1, 0 => ⟨20, by decide⟩
    | 2, 2, 1, 0 => ⟨21, by decide⟩
    | 0, 2, 1, 0 => ⟨22, by decide⟩
    | 1, 0, 1, 0 => ⟨23, by decide⟩
    | 2, 0, 1, 1 => ⟨24, by decide⟩
    | 0, 0, 2, 1 => ⟨25, by decide⟩
    | 1, 1, 2, 1 => ⟨26, by decide⟩
    | 0, 1, 2, 1 => ⟨27, by decide⟩
    | 1, 2, 2, 1 => ⟨28, by decide⟩
    | 2, 0, 2, 1 => ⟨29, by decide⟩
    | 0, 0, 0, 1 => ⟨30, by decide⟩
    | 1, 1, 0, 1 => ⟨31, by decide⟩
    | 2, 2, 0, 1 => ⟨32, by decide⟩
    | 1, 2, 0, 1 => ⟨33, by decide⟩
    | 2, 0, 0, 1 => ⟨34, by decide⟩
    | 0, 0, 1, 1 => ⟨35, by decide⟩
    | 1, 0, 1, 2 => ⟨36, by decide⟩
    | 2, 1, 1, 2 => ⟨37, by decide⟩
    | 0, 1, 2, 2 => ⟨38, by decide⟩
    | 2, 1, 2, 2 => ⟨39, by decide⟩
    | 0, 1, 0, 2 => ⟨40, by decide⟩
    | 1, 2, 0, 2 => ⟨41, by decide⟩
    | 0, 2, 0, 2 => ⟨42, by decide⟩
    | 1, 0, 0, 2 => ⟨43, by decide⟩
    | 2, 1, 0, 2 => ⟨44, by decide⟩
    | 1, 1, 0, 2 => ⟨45, by decide⟩
    | 2, 2, 0, 2 => ⟨46, by decide⟩
    | 0, 2, 1, 2 => ⟨47, by decide⟩
    | 2, 2, 1, 2 => ⟨48, by decide⟩
    | 0, 2, 2, 2 => ⟨49, by decide⟩
    | 1, 0, 2, 2 => ⟨50, by decide⟩
    | 2, 0, 2, 0 => ⟨51, by decide⟩
    | 0, 0, 2, 0 => ⟨52, by decide⟩
    | 1, 0, 2, 1 => ⟨53, by decide⟩
    | 2, 1, 2, 1 => ⟨54, by decide⟩
    | 0, 1, 0, 1 => ⟨55, by decide⟩
    | 2, 1, 0, 1 => ⟨56, by decide⟩
    | 0, 1, 1, 1 => ⟨57, by decide⟩
    | 1, 2, 1, 1 => ⟨58, by decide⟩
    | 0, 2, 1, 1 => ⟨59, by decide⟩
    | 1, 0, 1, 1 => ⟨60, by decide⟩
    | 2, 1, 1, 1 => ⟨61, by decide⟩
    | 1, 1, 1, 1 => ⟨62, by decide⟩
    | 2, 2, 1, 1 => ⟨63, by decide⟩
    | 0, 2, 2, 1 => ⟨64, by decide⟩
    | 2, 2, 2, 1 => ⟨65, by decide⟩
    | 0, 2, 0, 1 => ⟨66, by decide⟩
    | 1, 0, 0, 1 => ⟨67, by decide⟩
    | 2, 0, 0, 2 => ⟨68, by decide⟩
    | 0, 0, 1, 2 => ⟨69, by decide⟩
    | 1, 1, 1, 2 => ⟨70, by decide⟩
    | 0, 1, 1, 2 => ⟨71, by decide⟩
    | 1, 2, 1, 2 => ⟨72, by decide⟩
    | 2, 0, 1, 2 => ⟨73, by decide⟩
    | 0, 0, 2, 2 => ⟨74, by decide⟩
    | 1, 1, 2, 2 => ⟨75, by decide⟩
    | 2, 2, 2, 2 => ⟨76, by decide⟩
    | 1, 2, 2, 2 => ⟨77, by decide⟩
    | 2, 0, 2, 2 => ⟨78, by decide⟩
    | 0, 0, 0, 2 => ⟨79, by decide⟩
    | 1, 0, 0, 0 => ⟨80, by decide⟩
    | _, _, _, _ => ⟨0, by decide⟩
  | 2 =>
    match (x 0).val, (x 1).val, (x 2).val, (x 3).val with
    | 0, 0, 0, 0 => ⟨0, by decide⟩
    | 1, 1, 0, 0 => ⟨1, by decide⟩
    | 2, 0, 0, 0 => ⟨2, by decide⟩
    | 0, 2, 0, 0 => ⟨3, by decide⟩
    | 1, 0, 1, 0 => ⟨4, by decide⟩
    | 2, 2, 1, 0 => ⟨5, by decide⟩
    | 0, 1, 1, 0 => ⟨6, by decide⟩
    | 1, 2, 1, 1 => ⟨7, by decide⟩
    | 0, 0, 1, 1 => ⟨8, by decide⟩
    | 1, 1, 1, 2 => ⟨9, by decide⟩
    | 2, 2, 2, 2 => ⟨10, by decide⟩
    | 1, 0, 2, 2 => ⟨11, by decide⟩
    | 2, 1, 0, 2 => ⟨12, by decide⟩
    | 0, 2, 1, 2 => ⟨13, by decide⟩
    | 2, 0, 1, 2 => ⟨14, by decide⟩
    | 0, 1, 2, 2 => ⟨15, by decide⟩
    | 1, 2, 2, 0 => ⟨16, by decide⟩
    | 2, 1, 2, 0 => ⟨17, by decide⟩
    | 0, 0, 2, 0 => ⟨18, by decide⟩
    | 1, 1, 2, 1 => ⟨19, by decide⟩
    | 2, 2, 0, 1 => ⟨20, by decide⟩
    | 1, 0, 0, 1 => ⟨21, by decide⟩
    | 2, 1, 1, 1 => ⟨22, by decide⟩
    | 0, 2, 2, 1 => ⟨23, by decide⟩
    | 2, 0, 2, 1 => ⟨24, by decide⟩
    | 0, 1, 0, 1 => ⟨25, by decide⟩
    | 1, 2, 0, 1 => ⟨26, by decide⟩
    | 2, 0, 0, 2 => ⟨27, by decide⟩
    | 0, 1, 1, 2 => ⟨28, by decide⟩
    | 1, 0, 1, 2 => ⟨29, by decide⟩
    | 2, 1, 2, 2 => ⟨30, by decide⟩
    | 0, 2, 0, 2 => ⟨31, by decide⟩
    | 1, 0, 0, 0 => ⟨32, by decide⟩
    | 2, 1, 1, 0 => ⟨33, by decide⟩
    | 0, 2, 2, 0 => ⟨34, by decide⟩
    | 1, 1, 2, 0 => ⟨35, by decide⟩
    | 2, 2, 0, 0 => ⟨36, by decide⟩
    | 0, 0, 0, 1 => ⟨37, by decide⟩
    | 1, 1, 0, 1 => ⟨38, by decide⟩
    | 2, 2, 1, 1 => ⟨39, by decide⟩
    | 0, 0, 1, 2 => ⟨40, by decide⟩
    | 1, 2, 1, 2 => ⟨41, by decide⟩
    | 2, 0, 1, 0 => ⟨42, by decide⟩
    | 0, 1, 2, 0 => ⟨43, by decide⟩
    | 1, 0, 2, 0 => ⟨44, by decide⟩
    | 2, 1, 0, 0 => ⟨45, by decide⟩
    | 0, 2, 1, 0 => ⟨46, by decide⟩
    | 1, 1, 1, 0 => ⟨47, by decide⟩
    | 2, 2, 2, 0 => ⟨48, by decide⟩
    | 0, 0, 2, 1 => ⟨49, by decide⟩
    | 1, 2, 2, 1 => ⟨50, by decide⟩
    | 2, 0, 2, 2 => ⟨51, by decide⟩
    | 0, 1, 0, 2 => ⟨52, by decide⟩
    | 1, 2, 0, 2 => ⟨53, by decide⟩
    | 0, 0, 0, 2 => ⟨54, by decide⟩
    | 1, 1, 0, 2 => ⟨55, by decide⟩
    | 2, 2, 1, 2 => ⟨56, by decide⟩
    | 0, 0, 1, 0 => ⟨57, by decide⟩
    | 1, 2, 1, 0 => ⟨58, by decide⟩
    | 2, 0, 1, 1 => ⟨59, by decide⟩
    | 0, 1, 2, 1 => ⟨60, by decide⟩
    | 1, 0, 2, 1 => ⟨61, by decide⟩
    | 2, 1, 0, 1 => ⟨62, by decide⟩
    | 0, 2, 1, 1 => ⟨63, by decide⟩
    | 1, 1, 1, 1 => ⟨64, by decide⟩
    | 2, 2, 2, 1 => ⟨65, by decide⟩
    | 0, 0, 2, 2 => ⟨66, by decide⟩
    | 1, 2, 2, 2 => ⟨67, by decide⟩
    | 2, 0, 2, 0 => ⟨68, by decide⟩
    | 0, 1, 0, 0 => ⟨69, by decide⟩
    | 1, 2, 0, 0 => ⟨70, by decide⟩
    | 2, 0, 0, 1 => ⟨71, by decide⟩
    | 0, 1, 1, 1 => ⟨72, by decide⟩
    | 1, 0, 1, 1 => ⟨73, by decide⟩
    | 2, 1, 2, 1 => ⟨74, by decide⟩
    | 0, 2, 0, 1 => ⟨75, by decide⟩
    | 1, 0, 0, 2 => ⟨76, by decide⟩
    | 2, 1, 1, 2 => ⟨77, by decide⟩
    | 0, 2, 2, 2 => ⟨78, by decide⟩
    | 1, 1, 2, 2 => ⟨79, by decide⟩
    | 2, 2, 0, 2 => ⟨80, by decide⟩
    | _, _, _, _ => ⟨0, by decide⟩
  | 3 =>
    match (x 0).val, (x 1).val, (x 2).val, (x 3).val with
    | 0, 0, 0, 0 => ⟨0, by decide⟩
    | 1, 1, 1, 0 => ⟨1, by decide⟩
    | 1, 2, 2, 1 => ⟨2, by decide⟩
    | 1, 0, 0, 1 => ⟨3, by decide⟩
    | 1, 1, 2, 1 => ⟨4, by decide⟩
    | 1, 2, 0, 1 => ⟨5, by decide⟩
    | 1, 0, 1, 2 => ⟨6, by decide⟩
    | 1, 1, 0, 2 => ⟨7, by decide⟩
    | 1, 2, 1, 0 => ⟨8, by decide⟩
    | 1, 0, 2, 1 => ⟨9, by decide⟩
    | 1, 1, 1, 1 => ⟨10, by decide⟩
    | 1, 2, 2, 2 => ⟨11, by decide⟩
    | 1, 0, 0, 2 => ⟨12, by decide⟩
    | 1, 1, 2, 2 => ⟨13, by decide⟩
    | 1, 2, 0, 2 => ⟨14, by decide⟩
    | 1, 0, 1, 0 => ⟨15, by decide⟩
    | 2, 1, 2, 0 => ⟨16, by decide⟩
    | 2, 2, 0, 0 => ⟨17, by decide⟩
    | 2, 0, 1, 1 => ⟨18, by decide⟩
    | 2, 1, 0, 1 => ⟨19, by decide⟩
    | 2, 2, 1, 2 => ⟨20, by decide⟩
    | 2, 0, 2, 0 => ⟨21, by decide⟩
    | 2, 1, 0, 0 => ⟨22, by decide⟩
    | 2, 2, 1, 1 => ⟨23, by decide⟩
    | 2, 0, 2, 2 => ⟨24, by decide⟩
    | 2, 1, 1, 2 => ⟨25, by decide⟩
    | 2, 2, 2, 0 => ⟨26, by decide⟩
    | 2, 0, 0, 0 => ⟨27, by decide⟩
    | 0, 1, 1, 0 => ⟨28, by decide⟩
    | 0, 2, 0, 0 => ⟨29, by decide⟩
    | 0, 0, 2, 0 => ⟨30, by decide⟩
    | 0, 1, 0, 1 => ⟨31, by decide⟩
    | 0, 2, 2, 1 => ⟨32, by decide⟩
    | 0, 0, 1, 1 => ⟨33, by decide⟩
    | 0, 1, 2, 1 => ⟨34, by decide⟩
    | 0, 0, 0, 1 => ⟨35, by decide⟩
    | 0, 1, 1, 1 => ⟨36, by decide⟩
    | 0, 2, 2, 2 => ⟨37, by decide⟩
    | 0, 1, 0, 2 => ⟨38, by decide⟩
    | 0, 2, 1, 0 => ⟨39, by decide⟩
    | 0, 0, 2, 1 => ⟨40, by decide⟩
    | 0, 2, 0, 1 => ⟨41, by decide⟩
    | 0, 0, 1, 2 => ⟨42, by decide⟩
    | 0, 1, 2, 2 => ⟨43, by decide⟩
    | 0, 2, 1, 2 => ⟨44, by decide⟩
    | 0, 0, 0, 2 => ⟨45, by decide⟩
    | 0, 1, 1, 2 => ⟨46, by decide⟩
    | 0, 2, 2, 0 => ⟨47, by decide⟩
    | 0, 1, 0, 0 => ⟨48, by decide⟩
    | 0, 2, 1, 1 => ⟨49, by decide⟩
    | 0, 0, 2, 2 => ⟨50, by decide⟩
    | 0, 2, 0, 2 => ⟨51, by decide⟩
    | 0, 0, 1, 0 => ⟨52, by decide⟩
    | 1, 1, 2, 0 => ⟨53, by decide⟩
    | 1, 2, 0, 0 => ⟨54, by decide⟩
    | 1, 0, 1, 1 => ⟨55, by decide⟩
    | 1, 1, 0, 1 => ⟨56, by decide⟩
    | 1, 2, 1, 2 => ⟨57, by decide⟩
    | 1, 0, 2, 0 => ⟨58, by decide⟩
    | 1, 1, 0, 0 => ⟨59, by decide⟩
    | 1, 2, 1, 1 => ⟨60, by decide⟩
    | 1, 0, 2, 2 => ⟨61, by decide⟩
    | 1, 1, 1, 2 => ⟨62, by decide⟩
    | 1, 2, 2, 0 => ⟨63, by decide⟩
    | 1, 0, 0, 0 => ⟨64, by decide⟩
    | 2, 1, 1, 0 => ⟨65, by decide⟩
    | 2, 2, 2, 1 => ⟨66, by decide⟩
    | 2, 0, 0, 1 => ⟨67, by decide⟩
    | 2, 1, 2, 1 => ⟨68, by decide⟩
    | 2, 2, 0, 1 => ⟨69, by decide⟩
    | 2, 0, 1, 2 => ⟨70, by decide⟩
    | 2, 1, 0, 2 => ⟨71, by decide⟩
    | 2, 2, 1, 0 => ⟨72, by decide⟩
    | 2, 0, 2, 1 => ⟨73, by decide⟩
    | 2, 1, 1, 1 => ⟨74, by decide⟩
    | 2, 2, 2, 2 => ⟨75, by decide⟩
    | 2, 0, 0, 2 => ⟨76, by decide⟩
    | 2, 1, 2, 2 => ⟨77, by decide⟩
    | 2, 2, 0, 2 => ⟨78, by decide⟩
    | 2, 0, 1, 0 => ⟨79, by decide⟩
    | 0, 1, 2, 0 => ⟨80, by decide⟩
    | _, _, _, _ => ⟨0, by decide⟩
  | 4 =>
    match (x 0).val, (x 1).val, (x 2).val, (x 3).val with
    | 0, 0, 0, 0 => ⟨0, by decide⟩
    | 1, 0, 1, 1 => ⟨1, by decide⟩
    | 1, 0, 2, 2 => ⟨2, by decide⟩
    | 1, 0, 1, 0 => ⟨3, by decide⟩
    | 1, 0, 2, 1 => ⟨4, by decide⟩
    | 1, 0, 0, 2 => ⟨5, by decide⟩
    | 1, 0, 2, 0 => ⟨6, by decide⟩
    | 1, 0, 0, 1 => ⟨7, by decide⟩
    | 1, 1, 1, 2 => ⟨8, by decide⟩
    | 2, 1, 2, 0 => ⟨9, by decide⟩
    | 2, 1, 0, 1 => ⟨10, by decide⟩
    | 2, 1, 1, 0 => ⟨11, by decide⟩
    | 2, 1, 2, 1 => ⟨12, by decide⟩
    | 2, 1, 0, 2 => ⟨13, by decide⟩
    | 0, 1, 1, 0 => ⟨14, by decide⟩
    | 0, 1, 2, 1 => ⟨15, by decide⟩
    | 0, 1, 0, 2 => ⟨16, by decide⟩
    | 0, 1, 1, 1 => ⟨17, by decide⟩
    | 0, 1, 2, 2 => ⟨18, by decide⟩
    | 1, 1, 0, 0 => ⟨19, by decide⟩
    | 1, 2, 1, 1 => ⟨20, by decide⟩
    | 1, 2, 2, 2 => ⟨21, by decide⟩
    | 2, 2, 0, 0 => ⟨22, by decide⟩
    | 2, 2, 1, 2 => ⟨23, by decide⟩
    | 0, 2, 2, 0 => ⟨24, by decide⟩
    | 0, 2, 0, 1 => ⟨25, by decide⟩
    | 0, 2, 1, 0 => ⟨26, by decide⟩
    | 0, 2, 2, 1 => ⟨27, by decide⟩
    | 0, 2, 0, 2 => ⟨28, by decide⟩
    | 0, 2, 1, 1 => ⟨29, by decide⟩
    | 0, 2, 2, 2 => ⟨30, by decide⟩
    | 1, 2, 0, 0 => ⟨31, by decide⟩
    | 1, 2, 1, 2 => ⟨32, by decide⟩
    | 2, 2, 2, 0 => ⟨33, by decide⟩
    | 2, 2, 0, 1 => ⟨34, by decide⟩
    | 2, 0, 1, 2 => ⟨35, by decide⟩
    | 2, 0, 0, 0 => ⟨36, by decide⟩
    | 2, 1, 1, 1 => ⟨37, by decide⟩
    | 2, 1, 2, 2 => ⟨38, by decide⟩
    | 0, 1, 0, 0 => ⟨39, by decide⟩
    | 0, 1, 1, 2 => ⟨40, by decide⟩
    | 1, 1, 2, 0 => ⟨41, by decide⟩
    | 1, 1, 0, 1 => ⟨42, by decide⟩
    | 1, 1, 1, 0 => ⟨43, by decide⟩
    | 1, 1, 2, 1 => ⟨44, by decide⟩
    | 1, 1, 0, 2 => ⟨45, by decide⟩
    | 1, 1, 1, 1 => ⟨46, by decide⟩
    | 1, 1, 2, 2 => ⟨47, by decide⟩
    | 2, 1, 0, 0 => ⟨48, by decide⟩
    | 2, 1, 1, 2 => ⟨49, by decide⟩
    | 0, 1, 2, 0 => ⟨50, by decide⟩
    | 0, 1, 0, 1 => ⟨51, by decide⟩
    | 0, 2, 1, 2 => ⟨52, by decide⟩
    | 1, 2, 2, 0 => ⟨53, by decide⟩
    | 1, 2, 0, 1 => ⟨54, by decide⟩
    | 1, 2, 1, 0 => ⟨55, by decide⟩
    | 1, 2, 2, 1 => ⟨56, by decide⟩
    | 1, 2, 0, 2 => ⟨57, by decide⟩
    | 2, 2, 1, 0 => ⟨58, by decide⟩
    | 2, 2, 2, 1 => ⟨59, by decide⟩
    | 2, 2, 0, 2 => ⟨60, by decide⟩
    | 2, 2, 1, 1 => ⟨61, by decide⟩
    | 2, 2, 2, 2 => ⟨62, by decide⟩
    | 0, 2, 0, 0 => ⟨63, by decide⟩
    | 0, 0, 1, 1 => ⟨64, by decide⟩
    | 0, 0, 2, 0 => ⟨65, by decide⟩
    | 0, 0, 0, 2 => ⟨66, by decide⟩
    | 0, 0, 1, 0 => ⟨67, by decide⟩
    | 0, 0, 2, 2 => ⟨68, by decide⟩
    | 0, 0, 0, 1 => ⟨69, by decide⟩
    | 1, 0, 1, 2 => ⟨70, by decide⟩
    | 1, 0, 0, 0 => ⟨71, by decide⟩
    | 2, 0, 1, 1 => ⟨72, by decide⟩
    | 2, 0, 2, 2 => ⟨73, by decide⟩
    | 2, 0, 1, 0 => ⟨74, by decide⟩
    | 2, 0, 2, 1 => ⟨75, by decide⟩
    | 2, 0, 0, 2 => ⟨76, by decide⟩
    | 2, 0, 2, 0 => ⟨77, by decide⟩
    | 2, 0, 0, 1 => ⟨78, by decide⟩
    | 0, 0, 1, 2 => ⟨79, by decide⟩
    | 0, 0, 2, 1 => ⟨80, by decide⟩
    | _, _, _, _ => ⟨0, by decide⟩

set_option maxHeartbeats 3000000 in
-- Checks the generated five-color, 81-state m=3 rank certificate.
set_option linter.style.nativeDecide false in
theorem m3Rank_step :
    forall c : Color, forall x : Fin 4 -> ZMod 3,
      m3Rank c (m3ReturnQuad c x) = fin81AddNat (m3Rank c x) 1 := by
  native_decide

set_option maxHeartbeats 3000000 in
-- Checks that each generated rank table is a bijection onto Fin 81.
set_option linter.style.nativeDecide false in
theorem m3Rank_bijective : forall c : Color, Function.Bijective (m3Rank c) := by
  native_decide

theorem m3Rank_orbit_nat (c : Color) :
    forall (k : Nat) (x : Fin 4 -> ZMod 3),
      m3Rank c ((m3ReturnQuad c)^[k] x) = fin81AddNat (m3Rank c x) k := by
  intro k
  induction k with
  | zero =>
      intro x
      simp [fin81AddNat_zero]
  | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply']
      rw [m3Rank_step c]
      rw [ih]
      rw [fin81AddNat_add]

theorem m3Rank_orbit (c : Color) :
    forall (x : Fin 4 -> ZMod 3) (n : Fin 81),
      m3Rank c ((m3ReturnQuad c)^[n.val] x) = fin81AddNat (m3Rank c x) n.val := by
  intro x n
  exact m3Rank_orbit_nat c n.val x

theorem m3ReturnQuad_single_cycle (c : Color) :
    IsSingleCycleMap (m3ReturnQuad c) := by
  exact single_cycle_of_rank
    (f := m3ReturnQuad c)
    (rank := m3Rank c)
    (m3Rank_bijective c)
    (m3Rank_step c)
    (m3Rank_orbit c)

theorem colorReturn_m3_single_cycle (c : Color) :
    IsSingleCycleMap (colorReturn m3Schedule c) := by
  exact single_cycle_of_bijective_semiconj
    (f := m3ReturnQuad c)
    (g := colorReturn m3Schedule c)
    (phi := rootOfQuad)
    (Equiv.bijective (rootQuadEquiv 3))
    (by intro x; unfold m3ReturnQuad; rw [rootOfQuad_quadOfRoot])
    (m3ReturnQuad_single_cycle c)

theorem m3Rank_step_zmod (c : Color) (x : Fin 4 -> ZMod 3) :
    (ZMod.finEquiv 81) (m3Rank c (m3ReturnQuad c x)) =
      (ZMod.finEquiv 81) (m3Rank c x) + 1 := by
  rw [m3Rank_step c x]
  exact fin81AddNat_one_zmod (m3Rank c x)

noncomputable def m3ReturnQuad_cycleCoordinate (c : Color) :
    Shared.CycleCoordinate 81 (m3ReturnQuad c) :=
  Shared.CycleCoordinate.ofFinRank
    (m3Rank c)
    (m3Rank_bijective c)
    (m3Rank_step_zmod c)

noncomputable def colorReturn_m3_cycleCoordinate (c : Color) :
    Shared.CycleCoordinate 81 (colorReturn m3Schedule c) :=
  (m3ReturnQuad_cycleCoordinate c).conjOfBijective
    rootOfQuad
    (Equiv.bijective (rootQuadEquiv 3))
    (by intro x; unfold m3ReturnQuad; rw [rootOfQuad_quadOfRoot])

theorem m3Schedule_allColorHamiltonian : AllColorHamiltonian m3Schedule := by
  intro c
  exact colorReturn_m3_single_cycle c

end D5Odd
