-- STATUS: main-path
import TorusEven.Collar.Transport

namespace TorusEven.Collar

open Function Surgery

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {m : ℕ} [NeZero m]
variable (S : Equiv.Perm α) (U : Set α) [DecidablePred (· ∈ U)]
variable (δ : α → ZMod m)

def GapSupport : Prop :=
  ∀ u ∈ U, ∃ a ∈ U, a ∈ orbitSet S u ∧
    ∀ x ∈ orbitSet S u, δ x ≠ 0 → x ∈ openGap S U a

def orbitMarks (u : α) : Set (orbitSet S u) := {x | x.val ∈ U}

instance orbitMarksDecidable (u : α) : DecidablePred (· ∈ orbitMarks S U u) :=
  fun x => inferInstanceAs (Decidable (x.val ∈ U))

theorem oneGap_on_orbit (hunit : UnitCarry S δ) (u a : α) (ha : a ∈ U)
    (hau : a ∈ orbitSet S u)
    (hsupp : ∀ x ∈ orbitSet S u, δ x ≠ 0 → x ∈ openGap S U a) :
    OneGapConclusion (orbitPerm S u) (orbitMarks S U u) (fun x => δ x.val) ⟨a, hau⟩ := by
  apply oneGap _ _ _ _ (orbitPerm_singleCycle S u) ha _ (hunit u)
  intro x hx
  obtain ⟨k, hk, hkt, heq⟩ := hsupp x.val x.property hx
  refine ⟨k, hk, ?_, Subtype.ext ((orbitPerm_iterate_val S u _ k).trans heq)⟩
  rwa [← retTime_semiconj (orbitPerm S u) (orbitMarks S U u) S U Subtype.val
    (fun _ => rfl) (fun _ => Iff.rfl) ha]

theorem relative_return (hunit : UnitCarry S δ) (hsupp : GapSupport S U δ)
    {u : α} (hu : u ∈ U) :
    ret (lift S δ) (zeroSection U) (u, 0) = (ret S U u, 0) := by
  obtain ⟨a, ha, hau, hgap⟩ := hsupp u hu
  have h := oneGap_on_orbit S U δ hunit u a ha hau hgap
  let u' : orbitSet S u := ⟨u, self_mem_orbitSet S u⟩
  let f : orbitSet S u × ZMod m → α × ZMod m := fun p => (p.1.val, p.2)
  have hf : Semiconj f (lift (orbitPerm S u) (fun x => δ x.val)) (lift S δ) :=
    fun _ => rfl
  have hr := ret_semiconj (lift (orbitPerm S u) (fun x => δ x.val))
    (zeroSection (orbitMarks S U u)) (lift S δ) (zeroSection U) f hf
    (fun _ => Iff.rfl) (show (u', 0) ∈ zeroSection (orbitMarks S U u) from ⟨hu, rfl⟩)
  rw [h.return_eq u' hu] at hr
  have hbase := ret_semiconj (orbitPerm S u) (orbitMarks S U u) S U Subtype.val
    (fun _ => rfl) (fun _ => Iff.rfl) (show u' ∈ orbitMarks S U u from hu)
  exact hr.symm.trans (Prod.ext hbase rfl)

theorem relative_renewal (hunit : UnitCarry S δ) (hsupp : GapSupport S U δ)
    {u : α} (hu : u ∈ U) :
    ∃ a ∈ U, a ∈ orbitSet S u ∧ ∀ x ∈ orbitSet S u, ∀ t : ZMod m,
      t ≠ 0 → (x, t) ∈ openGap (lift S δ) (zeroSection U) (a, 0) := by
  obtain ⟨a, ha, hau, hgap⟩ := hsupp u hu
  have h := oneGap_on_orbit S U δ hunit u a ha hau hgap
  refine ⟨a, ha, hau, ?_⟩
  intro x hx t ht
  let f : orbitSet S u × ZMod m → α × ZMod m := fun p => (p.1.val, p.2)
  exact openGap_map (lift (orbitPerm S u) (fun x => δ x.val))
    (zeroSection (orbitMarks S U u)) (lift S δ) (zeroSection U) f
    (fun _ => rfl) (fun _ => Iff.rfl)
    (show (⟨a, hau⟩, 0) ∈ zeroSection (orbitMarks S U u) from ⟨ha, rfl⟩)
    (h.renewal ⟨x, hx⟩ t ht)

omit [NeZero m] in
theorem voltage_zero_at_marks (hsupp : GapSupport S U δ) {u : α} (hu : u ∈ U) : δ u = 0 := by
  obtain ⟨a, ha, _, hgap⟩ := hsupp u hu
  by_contra h
  exact openGap_not_mem S U ha (hgap u (self_mem_orbitSet S u) h) hu

theorem relative_transport (hunit : UnitCarry S δ) (hsupp : GapSupport S U δ)
    (r : Equiv.Perm U) :
    circuitCount (patch (lift S δ) (zeroSection U) (boundaryLift U r)) =
      circuitCount (patch S U r) :=
  transport_circuitCount S U δ hunit (fun _ hu => relative_return S U δ hunit hsupp hu) r

theorem relative_transport_hamilton [Nonempty α]
    (hunit : UnitCarry S δ) (hsupp : GapSupport S U δ) (r : Equiv.Perm U)
    (h : Shared.IsSingleCycleMap (patch S U r)) :
    Shared.IsSingleCycleMap (patch (lift S δ) (zeroSection U) (boundaryLift U r)) := by
  apply singleCycle_of_circuitCount_one
  rw [relative_transport S U δ hunit hsupp r]
  exact circuitCount_one_of_singleCycle _ h

end TorusEven.Collar
