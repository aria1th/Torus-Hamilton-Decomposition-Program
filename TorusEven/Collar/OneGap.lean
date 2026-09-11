-- STATUS: main-path
import TorusEven.Collar.FirstReturn
import TorusEven.Collar.Lift

namespace TorusEven.Collar

open Function Surgery

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {m : ℕ} [NeZero m]
variable (S : Equiv.Perm α) (U : Set α) [DecidablePred (· ∈ U)]
variable (δ : α → ZMod m) (a : α)

instance zeroSectionDecidable : DecidablePred (· ∈ zeroSection (m := m) U) :=
  fun p => inferInstanceAs (Decidable (p.1 ∈ U ∧ p.2 = 0))

omit [NeZero m] in
theorem carry_eq_zero_on_other_gap (ha : a ∈ U)
    (hsupp : ∀ x, δ x ≠ 0 → x ∈ openGap S U a)
    {u : α} (hu : u ∈ U) (hne : u ≠ a) (k : ℕ) (hk : k < retTime S U u) :
    δ (S^[k] u) = 0 := by
  by_contra hδ
  have hgap := hsupp _ hδ
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact openGap_not_mem S U ha hgap hu
  · obtain ⟨j, hj, hja, heq⟩ := hgap
    exact hne (segment_indices_eq S U hu ha hk0 hk.le hj hja.le heq.symm).1

theorem ordinary_return (ha : a ∈ U)
    (hsupp : ∀ x, δ x ≠ 0 → x ∈ openGap S U a)
    {u : α} (hu : u ∈ U) (hne : u ≠ a) :
    retTime (lift S δ) (zeroSection U) (u, 0) = retTime S U u ∧
      ret (lift S δ) (zeroSection U) (u, 0) = (ret S U u, 0) := by
  have hiter : ∀ k, k ≤ retTime S U u →
      (lift S δ)^[k] (u, 0) = (S^[k] u, 0) := by
    intro k hk
    exact lift_iterate_zero S δ u k
      (fun j hj => carry_eq_zero_on_other_gap S U δ a ha hsupp hu hne j (by omega))
  have htime : retTime (lift S δ) (zeroSection U) (u, 0) = retTime S U u := by
    apply retTime_eq_of_first (lift S δ) (zeroSection U)
      (show (u, 0) ∈ zeroSection U from ⟨hu, rfl⟩)
      (retTime_pos S U hu)
    · rw [hiter _ le_rfl]
      exact ⟨ret_mem S U hu, rfl⟩
    · intro k hk0 hkt
      rw [hiter k hkt.le]
      exact fun h => not_mem_of_lt_retTime S U hu hk0 hkt h.1
  refine ⟨htime, ?_⟩
  unfold ret
  rw [htime, hiter _ le_rfl]

structure OneGapConclusion : Prop where
  singleCycle : Shared.IsSingleCycleMap (lift S δ)
  return_eq : ∀ u ∈ U, ret (lift S δ) (zeroSection U) (u, 0) = (ret S U u, 0)
  roof_eq : ∀ u ∈ U, retTime (lift S δ) (zeroSection U) (u, 0) =
    retTime S U u + if u = a then (m - 1) * Fintype.card α else 0
  renewal : ∀ x (t : ZMod m), t ≠ 0 → (x, t) ∈ openGap (lift S δ) (zeroSection U) (a, 0)

theorem oneGap (hS : Shared.IsSingleCycleMap S) (ha : a ∈ U)
    (hsupp : ∀ x, δ x ≠ 0 → x ∈ openGap S U a)
    (hunit : IsUnit (∑ x, δ x)) : OneGapConclusion S U δ a := by
  let L := lift S δ
  let V := zeroSection (m := m) U
  have hL : Shared.IsSingleCycleMap L := lift_singleCycle S hS δ a hunit
  have hmeet : ∀ x, ∃ w ∈ U, w ∈ orbitSet S x := fun x => ⟨a, ha, hS.2 x a⟩
  have hmeetL : ∀ x, ∃ w ∈ V, w ∈ orbitSet L x := fun x =>
    ⟨(a, 0), ⟨ha, rfl⟩, hL.2 x (a, 0)⟩
  have hord {u : α} (hu : u ∈ U) (hne : u ≠ a) :=
    ordinary_return S U δ a ha hsupp hu hne
  let e := zeroEquiv (m := m) U
  let f : U ≃ U := e.trans ((retPerm L V).trans e.symm)
  have hfg : (f : U → U) = retPerm S U := by
    apply eq_of_bijective_except f (retPerm S U) f.bijective (retPerm S U).injective ⟨a, ha⟩
    intro u hne
    apply Subtype.ext
    have hne' : u.val ≠ a := fun h => hne (Subtype.ext h)
    change (ret L V (u.val, 0)).1 = ret S U u.val
    rw [(hord u.property hne').2]
  have hreturn : ∀ u ∈ U, ret L V (u, 0) = (ret S U u, 0) := by
    intro u hu
    have hfst := congrArg Subtype.val (congrFun hfg ⟨u, hu⟩)
    have hsnd := (ret_mem L V (show (u, 0) ∈ V from ⟨hu, rfl⟩)).2
    exact Prod.ext hfst hsnd
  let oldRoof : U → ℕ := fun u => retTime S U u
  let newRoof : U → ℕ := fun u => retTime L V (u.val, 0)
  let aU : U := ⟨a, ha⟩
  have holdsum : ∑ u, oldRoof u = Fintype.card α := sum_retTime S U hmeet
  have hnewsum : ∑ u, newRoof u = Fintype.card α * m := by
    calc
      (∑ u, newRoof u) = ∑ v : V, retTime L V v :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = Fintype.card (α × ZMod m) := sum_retTime L V hmeetL
      _ = Fintype.card α * m := by simp
  have hrest : (∑ u ∈ Finset.univ.erase aU, newRoof u) =
      ∑ u ∈ Finset.univ.erase aU, oldRoof u := by
    apply Finset.sum_congr rfl
    intro u hu
    exact (hord u.property (fun h => (Finset.mem_erase.mp hu).1 (Subtype.ext h))).1
  have hnew := Finset.sum_erase_add Finset.univ newRoof (Finset.mem_univ aU)
  have hold := Finset.sum_erase_add Finset.univ oldRoof (Finset.mem_univ aU)
  rw [hrest, hnewsum] at hnew
  rw [holdsum] at hold
  have hm : 1 ≤ m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmul : Fintype.card α * m = Fintype.card α + (m - 1) * Fintype.card α := by
    nlinarith [Nat.sub_add_cancel hm]
  have hroof : newRoof aU = oldRoof aU + (m - 1) * Fintype.card α := by omega
  refine ⟨hL, hreturn, ?_, ?_⟩
  · intro u hu
    by_cases h : u = a
    · subst u
      simpa only [if_pos rfl] using hroof
    · simpa only [if_neg h, add_zero] using (hord hu h).1
  · intro x t ht
    let q := (segmentEquiv L V hmeetL).symm (x, t)
    have hq : L^[q.2.val + 1] q.1.val = (x, t) :=
      (segmentEquiv L V hmeetL).apply_symm_apply (x, t)
    have hv : q.1.val = (q.1.val.1, 0) := Prod.ext rfl q.1.property.2
    have hu : q.1.val.1 ∈ U := q.1.property.1
    have hua : q.1.val.1 = a := by
      by_contra hne
      have htime := (hord hu hne).1
      have hn : q.2.val + 1 ≤ retTime S U q.1.val.1 := by
        calc
          _ ≤ retTime L V q.1.val := q.2.isLt
          _ = retTime L V (q.1.val.1, 0) := congrArg (retTime L V) hv
          _ = retTime S U q.1.val.1 := htime
      have hzero := lift_iterate_zero S δ q.1.val.1 (q.2.val + 1)
        (fun k hk => carry_eq_zero_on_other_gap S U δ a ha hsupp hu hne k (by omega))
      have hq0 := (congrArg (fun p => L^[q.2.val + 1] p) hv).symm.trans hq
      rw [hzero] at hq0
      exact ht (congrArg Prod.snd hq0).symm
    have hva : q.1.val = (a, 0) := hv.trans (by rw [hua])
    have hn : q.2.val + 1 ≤ retTime L V (a, 0) := by
      exact q.2.isLt.trans_eq (congrArg (retTime L V) hva)
    have hqa := (congrArg (fun p => L^[q.2.val + 1] p) hva).symm.trans hq
    refine ⟨q.2.val + 1, by omega, ?_, hqa⟩
    apply lt_of_le_of_ne hn
    intro heq
    have hzero : L^[retTime L V (a, 0)] (a, 0) = (ret S U a, 0) := hreturn a ha
    rw [heq, hzero] at hqa
    exact ht (congrArg Prod.snd hqa).symm

end TorusEven.Collar
