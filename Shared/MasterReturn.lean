import Shared.SwitchCalculus
import Shared.Monodromy

/-!
# Master return single-cycle wrappers

These theorems package the two generic engines used by the EvenV11 certificate
families:

* cut/flag splicing produces a single base return cycle;
* unit carry lifts that base cycle to a single skew-product return cycle.

They are deliberately construction-agnostic. Concrete D5/D7/high-even/endpoint
rows only need to supply the packet hypotheses and the unit-carry sum.
-/

namespace Shared
namespace SwitchCalculus

open Equiv (Perm)

variable {α : Type*}

/-- Master one-step return wrapper: a packet splice that covers the whole base,
followed by a unit additive carry, gives a single skew-product return cycle. -/
theorem oneStepPacketSplice_unitCarrySingleCycle
    [Fintype α]
    {q : ℕ} [NeZero q] {m : Nat} [NeZero m]
    (R R' : Perm α)
    (C : ZMod q → Set α) (a h : ZMod q → α)
    (carry : α → ZMod m)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hmem : ∀ j, a j ∈ C j ∧ h j ∈ C j)
    (hHead : ∀ j, R (a j) = h j)
    (hCyc : ∀ j, R.IsCycleOn (C j))
    (hSplice : ∀ j, R' (a j) = h (j + 1))
    (hRest : ∀ x, (∀ k, x ≠ a k) → R' x = R x)
    (hcover : (⋃ j, C j) = Set.univ)
    (hcard : 1 < Fintype.card α)
    (hunit : IsUnit (∑ x : α, carry x)) :
    Shared.IsSingleCycleMap
      (Shared.skewProductMap R' (fun b z => z + carry b)) := by
  have hbase : Shared.IsSingleCycleMap R' :=
    oneStepPacketSplice_singleCycleMap R R' C a h hdisj hmem hHead hCyc
      hSplice hRest hcover
  exact Shared.single_cycle_of_skewProduct_zmod_additive_unit_sum_of_base_cycle
    R' carry hbase hcard hunit

theorem OneStepPacketSpliceCertificate.unitCarrySingleCycle
    [Fintype α]
    {q : ℕ} [NeZero q] {m : Nat} [NeZero m]
    {R R' : Perm α} {C : ZMod q → Set α} {a h : ZMod q → α}
    (cert : OneStepPacketSpliceCertificate R R' C a h)
    (carry : α → ZMod m)
    (cover : (⋃ j, C j) = Set.univ)
    (card : 1 < Fintype.card α)
    (unit : IsUnit (∑ x : α, carry x)) :
    Shared.IsSingleCycleMap
      (Shared.skewProductMap R' (fun b z => z + carry b)) :=
  oneStepPacketSplice_unitCarrySingleCycle R R' C a h carry
    cert.pairwiseDisjoint cert.mem cert.head cert.cycles cert.splice cert.rest
    cover card unit

/-- Master flag-layer return wrapper: a parallel flag-splicing layer whose
chosen final target cell covers the whole base, followed by a unit additive
carry, gives a single skew-product return cycle. -/
theorem flagSplicingCriterion_unitCarrySingleCycle
    [Fintype α]
    {ι : Type*} {m : Nat} [NeZero m]
    (q : ι → ℕ) (hne : ∀ i : ι, NeZero (q i))
    (R R' : Perm α)
    (D : ι → Set α)
    (C : ∀ i : ι, ZMod (q i) → Set α)
    (a h : ∀ i : ι, ZMod (q i) → α)
    (carry : α → ZMod m)
    (hcell : ∀ i : ι, D i = ⋃ j, C i j)
    (hpacketDisj : ∀ i i' : ι, i ≠ i' → Disjoint (D i) (D i'))
    (hdisj : ∀ i : ι, ∀ j k : ZMod (q i), j ≠ k → Disjoint (C i j) (C i k))
    (hmem : ∀ i : ι, ∀ j : ZMod (q i), a i j ∈ C i j ∧ h i j ∈ C i j)
    (hHead : ∀ i : ι, ∀ j : ZMod (q i), R (a i j) = h i j)
    (hCyc : ∀ i : ι, ∀ j : ZMod (q i), R.IsCycleOn (C i j))
    (hSplice : ∀ i : ι, ∀ j : ZMod (q i), R' (a i j) = h i (j + 1))
    (hRest :
      ∀ x, x ∈ (⋃ i, D i) →
        (∀ i : ι, ∀ j : ZMod (q i), x ≠ a i j) → R' x = R x)
    (top : ι) (hcover : D top = Set.univ)
    (hcard : 1 < Fintype.card α)
    (hunit : IsUnit (∑ x : α, carry x)) :
    Shared.IsSingleCycleMap
      (Shared.skewProductMap R' (fun b z => z + carry b)) := by
  have hbase : Shared.IsSingleCycleMap R' :=
    flagSplicingCriterion_singleCycleMap q hne R R' D C a h hcell hpacketDisj
      hdisj hmem hHead hCyc hSplice hRest top hcover
  exact Shared.single_cycle_of_skewProduct_zmod_additive_unit_sum_of_base_cycle
    R' carry hbase hcard hunit

theorem FlagSplicingCertificate.unitCarrySingleCycle
    [Fintype α]
    {ι : Type*} {m : Nat} [NeZero m]
    {q : ι → ℕ} {R R' : Perm α}
    {D : ι → Set α}
    {C : ∀ i : ι, ZMod (q i) → Set α}
    {a h : ∀ i : ι, ZMod (q i) → α}
    (cert : FlagSplicingCertificate q R R' D C a h)
    (carry : α → ZMod m)
    (top : ι) (cover : D top = Set.univ)
    (card : 1 < Fintype.card α)
    (unit : IsUnit (∑ x : α, carry x)) :
    Shared.IsSingleCycleMap
      (Shared.skewProductMap R' (fun b z => z + carry b)) :=
  flagSplicingCriterion_unitCarrySingleCycle q cert.neZero R R' D C a h carry
    cert.cell cert.packetDisjoint cert.cosetDisjoint cert.mem cert.head
    cert.cycles cert.splice cert.rest top cover card unit

end SwitchCalculus
end Shared
