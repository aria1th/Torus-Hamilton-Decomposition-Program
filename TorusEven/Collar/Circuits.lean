-- STATUS: main-path
import TorusEven.Collar.FirstReturn

namespace TorusEven.Surgery

open Function

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (S : Equiv.Perm α) (U : Set α) [DecidablePred (· ∈ U)]

theorem retPerm_iterate_val (u : U) (n : ℕ) :
    ((retPerm S U)^[n] u).val = (ret S U)^[n] u.val := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterate_succ_apply', retPerm_apply, ih]

theorem orbit_retPerm_iff (u v : U) :
    v ∈ orbitSet (retPerm S U) u ↔ v.val ∈ orbitSet S u.val := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨k, hk⟩ := exists_iterate_comp_eq_afterRet_iterate S U id
      (fun _ _ => rfl) (fun _ h => h) u.property n
    refine ⟨k, hk.trans ?_⟩
    exact (retPerm_iterate_val S U u n).symm.trans (congrArg Subtype.val hn)
  · intro h
    have hseg := orbitSet_comp_eq S U id (fun _ _ => rfl)
      (fun _ h => h) Function.bijective_id u.property
    change v.val ∈ orbitSet (S ∘ id) u.val at h
    rw [hseg] at h
    obtain ⟨w, ⟨j, hj⟩, k, hk, hkt, hkv⟩ := Set.mem_iUnion₂.mp h
    have hw : w ∈ U := hj ▸ afterRet_iterate_mem S U id (fun _ h => h) u.property j
    have heq : k = retTime S U w := by
      by_contra hne
      exact not_mem_of_lt_retTime S U hw hk (lt_of_le_of_ne hkt hne) (hkv ▸ v.property)
    refine ⟨j + 1, Subtype.ext ?_⟩
    rw [retPerm_iterate_val, iterate_succ_apply']
    change (ret S U)^[j] u.val = w at hj
    rw [hj]
    exact (congrArg (fun n => S^[n] w) heq).symm.trans hkv

def circuitSetoid : Setoid α where
  r x y := y ∈ orbitSet S x
  iseqv := ⟨self_mem_orbitSet S, fun h => mem_orbitSet_symm S.injective h,
    fun hxy hyz => by rwa [orbitSet_eq_of_mem S.injective hxy] at hyz⟩

abbrev Circuit := Quotient (circuitSetoid S)

noncomputable def circuitCount : ℕ := Nat.card (Circuit S)

def circuitOf (x : α) : Circuit S := Quotient.mk _ x

@[simp] theorem circuitOf_eq (x y : α) :
    circuitOf S x = circuitOf S y ↔ y ∈ orbitSet S x := Quotient.eq

def Hits (q : Circuit S) : Prop := ∃ u : U, circuitOf S u.val = q

abbrev HitCircuit := {q : Circuit S // Hits S U q}
abbrev UnhitCircuit := {q : Circuit S // ¬ Hits S U q}

omit [DecidablePred (· ∈ U)] in
theorem hits_circuitOf (x : α) :
    Hits S U (circuitOf S x) ↔ ∃ u ∈ U, u ∈ orbitSet S x := by
  simp only [Hits, circuitOf_eq]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u.val, u.property, mem_orbitSet_symm S.injective hu⟩
  · rintro ⟨u, hu, horb⟩
    exact ⟨⟨u, hu⟩, mem_orbitSet_symm S.injective horb⟩

noncomputable def returnCircuitMap : Circuit (retPerm S U) → Circuit S :=
  Quotient.map Subtype.val (fun {u v} h => (orbit_retPerm_iff S U u v).mp h)

noncomputable def returnCircuitEquiv : Circuit (retPerm S U) ≃ HitCircuit S U :=
  Equiv.ofBijective (fun q => ⟨returnCircuitMap S U q, by
    induction q using Quotient.inductionOn with | _ u => exact ⟨u, rfl⟩⟩) (by
      constructor
      · intro q q' h
        induction q using Quotient.inductionOn with | _ u =>
          induction q' using Quotient.inductionOn with | _ v =>
            exact Quotient.sound ((orbit_retPerm_iff S U u v).mpr
              (Quotient.exact (congrArg Subtype.val h)))
      · rintro ⟨q, u, hu⟩
        exact ⟨circuitOf (retPerm S U) u, Subtype.ext hu⟩)

theorem circuitCount_eq_return_add_unhit :
    circuitCount S = circuitCount (retPerm S U) + Nat.card (UnhitCircuit S U) := by
  classical
  let e := (Equiv.sumCongr (returnCircuitEquiv S U)
    (Equiv.refl (UnhitCircuit S U))).trans (Equiv.sumCompl (Hits S U))
  exact (Nat.card_congr e).symm.trans Nat.card_sum

omit [DecidablePred (· ∈ U)]

omit [Fintype α] [DecidableEq α] in
theorem orbitSet_eq_of_eq_on_orbit (T : Equiv.Perm α) (x : α)
    (h : ∀ y ∈ orbitSet S x, S y = T y) : orbitSet S x = orbitSet T x := by
  have hiter : ∀ n, S^[n] x = T^[n] x := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [iterate_succ_apply', h (S^[n] x) ⟨n, rfl⟩, ih, iterate_succ_apply']
  ext y
  change (∃ n, S^[n] x = y) ↔ ∃ n, T^[n] x = y
  simp only [hiter]

theorem unhit_circuitOf_iff (x : α) :
    ¬ Hits S U (circuitOf S x) ↔ ∀ y ∈ orbitSet S x, y ∉ U := by
  rw [hits_circuitOf]
  aesop

theorem unhit_orbitSet_eq (T : Equiv.Perm α) (heq : ∀ x, x ∉ U → S x = T x)
    (q : UnhitCircuit S U) : orbitSet S q.val.out = orbitSet T q.val.out := by
  apply orbitSet_eq_of_eq_on_orbit
  have hq : ¬ Hits S U (circuitOf S q.val.out) := by
    simpa only [circuitOf, Quotient.out_eq] using q.property
  exact fun y hy => heq y ((unhit_circuitOf_iff S U _).mp hq y hy)

noncomputable def unhitCircuitMap (T : Equiv.Perm α)
    (heq : ∀ x, x ∉ U → S x = T x) (q : UnhitCircuit S U) : UnhitCircuit T U := by
  refine ⟨circuitOf T q.val.out, ?_⟩
  rw [unhit_circuitOf_iff, ← unhit_orbitSet_eq S U T heq q]
  apply (unhit_circuitOf_iff S U _).mp
  simpa only [circuitOf, Quotient.out_eq] using q.property

theorem unhitCircuitMap_inverse (T : Equiv.Perm α)
    (heq : ∀ x, x ∉ U → S x = T x) (q : UnhitCircuit S U) :
    unhitCircuitMap T U S (fun x hx => (heq x hx).symm)
      (unhitCircuitMap S U T heq q) = q := by
  apply Subtype.ext
  change circuitOf S (circuitOf T q.val.out).out = q.val
  have h : (circuitOf T q.val.out).out ∈ orbitSet T q.val.out :=
    (circuitOf_eq T _ _).mp (Quotient.out_eq _).symm
  rw [← unhit_orbitSet_eq S U T heq q] at h
  exact ((circuitOf_eq S _ _).mpr h).symm.trans (Quotient.out_eq q.val)

noncomputable def unhitCircuitEquiv (T : Equiv.Perm α)
    (heq : ∀ x, x ∉ U → S x = T x) : UnhitCircuit S U ≃ UnhitCircuit T U where
  toFun := unhitCircuitMap S U T heq
  invFun := unhitCircuitMap T U S (fun x hx => (heq x hx).symm)
  left_inv := unhitCircuitMap_inverse S U T heq
  right_inv := unhitCircuitMap_inverse T U S (fun x hx => (heq x hx).symm)

variable {β : Type*} [Fintype β] [DecidableEq β]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem orbit_equiv_iff (T : Equiv.Perm β) (e : α ≃ β) (he : Semiconj e S T)
    (x y : α) : e y ∈ orbitSet T (e x) ↔ y ∈ orbitSet S x := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, e.injective ((he.iterate_right n x).trans hn)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (he.iterate_right n x).symm.trans (congrArg e hn)⟩

noncomputable def circuitEquiv (T : Equiv.Perm β) (e : α ≃ β) (he : Semiconj e S T) :
    Circuit S ≃ Circuit T := Quotient.congr e (fun x y => (orbit_equiv_iff S T e he x y).symm)

theorem circuitCount_congr (T : Equiv.Perm β) (e : α ≃ β) (he : Semiconj e S T) :
    circuitCount S = circuitCount T := Nat.card_congr (circuitEquiv S T e he)

theorem singleCycle_of_circuitCount_one (h : circuitCount S = 1) :
    Shared.IsSingleCycleMap S := by
  have hsub := (Nat.card_eq_one_iff_unique.mp h).1
  exact ⟨S.bijective, fun x y => (circuitOf_eq S x y).mp (hsub.elim _ _)⟩

theorem circuitCount_one_of_singleCycle [Nonempty α] (h : Shared.IsSingleCycleMap S) :
    circuitCount S = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  refine ⟨⟨?_⟩, Nonempty.map (circuitOf S) ‹Nonempty α›⟩
  intro q q'
  induction q using Quotient.inductionOn with | _ x =>
    induction q' using Quotient.inductionOn with | _ y =>
      exact Quotient.sound (h.2 x y)

end TorusEven.Surgery
