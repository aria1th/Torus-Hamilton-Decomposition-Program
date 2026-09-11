-- STATUS: main-path
import TorusEven.Collar.RelativeLift

namespace TorusEven.Surgery

open Function

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (S : Equiv.Perm α) (U : Set α) [DecidablePred (· ∈ U)]

theorem exists_openGap {u x : α} (hu : u ∈ U) (hx : x ∈ orbitSet S u) (hxU : x ∉ U) :
    ∃ a ∈ U, a ∈ orbitSet S u ∧ x ∈ openGap S U a := by
  have hseg := orbitSet_comp_eq S U id (fun _ _ => rfl) (fun _ h => h)
    Function.bijective_id hu
  change orbitSet S u = _ at hseg
  rw [hseg] at hx
  obtain ⟨v, ⟨j, hj⟩, k, hk, hkt, hkx⟩ := Set.mem_iUnion₂.mp hx
  have hv : v ∈ U := hj ▸ afterRet_iterate_mem S U id (fun _ h => h) hu j
  obtain ⟨l, hl⟩ := exists_iterate_comp_eq_afterRet_iterate S U id
    (fun _ _ => rfl) (fun _ h => h) hu j
  refine ⟨v, hv, ⟨l, hl.trans hj⟩, k, hk, ?_, hkx⟩
  apply lt_of_le_of_ne hkt
  intro he
  rw [he] at hkx
  exact hxU (hkx ▸ ret_mem S U hv)

end TorusEven.Surgery

namespace TorusEven.Collar

open Surgery

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {m : ℕ} [NeZero m] (S : Equiv.Perm α) (δ : α → ZMod m)

def SingleVoltage : Prop := ∀ u, ∃ q ∈ orbitSet S u,
  ∀ x ∈ orbitSet S u, δ x = if x = q then 1 else 0

omit [NeZero m] [Fintype α] in
theorem singleVoltage_of_pair (q₀ q₁ : α)
    (hsep : q₁ ∉ orbitSet S q₀)
    (hmeet : ∀ u, q₀ ∈ orbitSet S u ∨ q₁ ∈ orbitSet S u)
    (hδ : ∀ x, δ x = if x = q₀ ∨ x = q₁ then 1 else 0) [Finite α] : SingleVoltage S δ := by
  letI := Fintype.ofFinite α
  have hnot {u : α} (h₀ : q₀ ∈ orbitSet S u) (h₁ : q₁ ∈ orbitSet S u) : False := by
    apply hsep
    rwa [orbitSet_eq_of_mem S.injective h₀]
  intro u
  rcases hmeet u with h₀ | h₁
  · refine ⟨q₀, h₀, fun x hx => ?_⟩
    have hx₁ : x ≠ q₁ := fun h => hnot h₀ (h ▸ hx)
    simp [hδ, hx₁]
  · refine ⟨q₁, h₁, fun x hx => ?_⟩
    have hx₀ : x ≠ q₀ := fun h => hnot (h ▸ hx) h₁
    simp [hδ, hx₀]

omit [NeZero m] [DecidableEq α] in
theorem unitCarry_of_singleCycle (hcycle : Shared.IsSingleCycleMap S)
    (hsum : IsUnit (∑ x, δ x)) : UnitCarry S δ := by
  classical
  intro u
  let e : orbitSet S u ≃ α := Equiv.subtypeUnivEquiv (hcycle.2 u)
  have he : (∑ x : orbitSet S u, δ x.val) = ∑ x, δ x := e.sum_comp δ
  rwa [he]

omit [NeZero m] in
theorem SingleVoltage.unit (h : SingleVoltage S δ) : UnitCarry S δ := by
  classical
  intro u
  obtain ⟨q, hq, heq⟩ := h u
  have hs : (∑ x : orbitSet S u, δ x.val) = 1 := by
    simp only [heq _ (Subtype.property _)]
    exact Finset.sum_eq_single (⟨q, hq⟩ : orbitSet S u)
      (fun x _ hx => if_neg (fun he => hx (Subtype.ext he))) (by simp) |>.trans (by simp)
  rw [hs]
  exact isUnit_one

omit [NeZero m] in
theorem gapSupport_of_single_source (U : Set α) [DecidablePred (· ∈ U)]
    (h : ∀ u ∈ U, ∃ q ∈ orbitSet S u, q ∉ U ∧
      ∀ x ∈ orbitSet S u, δ x ≠ 0 → x = q) : GapSupport S U δ := by
  intro u hu
  obtain ⟨q, hq, hqU, hδ⟩ := h u hu
  obtain ⟨a, ha, hau, hgap⟩ := exists_openGap S U hu hq hqU
  exact ⟨a, ha, hau, fun x hx hn => (hδ x hx hn).symm ▸ hgap⟩

end TorusEven.Collar
