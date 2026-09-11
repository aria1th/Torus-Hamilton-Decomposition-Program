-- STATUS: main-path
import TorusEven.Collar.Circuits
import TorusEven.Collar.Lift

namespace TorusEven.Collar

open Function Surgery

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (S : Equiv.Perm α)

noncomputable instance orbitFintype (x : α) : Fintype (orbitSet S x) := Fintype.ofFinite _

omit [Fintype α] [DecidableEq α] in
theorem apply_mem_orbit_iff [Finite α] (x y : α) :
    S y ∈ orbitSet S x ↔ y ∈ orbitSet S x := by
  classical
  letI := Fintype.ofFinite α
  constructor
  · intro h
    have hy := mem_orbitSet_symm S.injective (show S y ∈ orbitSet S y from ⟨1, rfl⟩)
    rwa [orbitSet_eq_of_mem S.injective h] at hy
  · rintro ⟨n, rfl⟩
    exact ⟨n + 1, Function.iterate_succ_apply' S n x⟩

def orbitPerm (x : α) : Equiv.Perm (orbitSet S x) :=
  S.subtypePerm (apply_mem_orbit_iff S x)

omit [DecidableEq α] in
theorem orbitPerm_iterate_val (x : α) (y : orbitSet S x) (n : ℕ) :
    ((orbitPerm S x)^[n] y).val = S^[n] y.val :=
  (show Semiconj Subtype.val (orbitPerm S x) S from fun _ => rfl).iterate_right n y

omit [DecidableEq α] in
theorem orbitPerm_singleCycle (x : α) : Shared.IsSingleCycleMap (orbitPerm S x) := by
  classical
  refine ⟨(orbitPerm S x).bijective, ?_⟩
  intro y z
  have hz : z.val ∈ orbitSet S y.val := by
    rw [orbitSet_eq_of_mem S.injective y.property]
    exact z.property
  obtain ⟨n, hn⟩ := hz
  exact ⟨n, Subtype.ext ((orbitPerm_iterate_val S x y n).trans hn)⟩

variable {m : ℕ} [NeZero m]

def UnitCarry (δ : α → ZMod m) : Prop := ∀ x, IsUnit (∑ y : orbitSet S x, δ y.val)

omit [DecidableEq α] in
theorem lift_orbit_iff (δ : α → ZMod m) (hunit : UnitCarry S δ)
    (p q : α × ZMod m) : q ∈ orbitSet (lift S δ) p ↔ q.1 ∈ orbitSet S p.1 := by
  classical
  constructor
  · rintro ⟨n, hn⟩
    have hproj : Semiconj Prod.fst (lift S δ) S := fun _ => rfl
    exact ⟨n, (hproj.iterate_right n p).symm.trans (congrArg Prod.fst hn)⟩
  · intro hq
    let p' : orbitSet S p.1 × ZMod m := (⟨p.1, self_mem_orbitSet S p.1⟩, p.2)
    let q' : orbitSet S p.1 × ZMod m := (⟨q.1, hq⟩, q.2)
    let δ' : orbitSet S p.1 → ZMod m := fun y => δ y.val
    have hcycle := lift_singleCycle (orbitPerm S p.1) (orbitPerm_singleCycle S p.1)
      δ' p'.1 (hunit p.1)
    obtain ⟨n, hn⟩ := hcycle.2 p' q'
    let f : orbitSet S p.1 × ZMod m → α × ZMod m := fun y => (y.1.val, y.2)
    have hf : Semiconj f (lift (orbitPerm S p.1) δ') (lift S δ) := fun _ => rfl
    exact ⟨n, (hf.iterate_right n p').symm.trans (congrArg f hn)⟩

noncomputable def liftCircuitEquiv (δ : α → ZMod m) (hunit : UnitCarry S δ) :
    Circuit (lift S δ) ≃ Circuit S :=
  Equiv.ofBijective (Quotient.map Prod.fst
    (fun {p q} h => (lift_orbit_iff S δ hunit p q).mp h)) (by
      constructor
      · intro q q' h
        induction q using Quotient.inductionOn with | _ x =>
          induction q' using Quotient.inductionOn with | _ y =>
            exact Quotient.sound ((lift_orbit_iff S δ hunit x y).mpr (Quotient.exact h))
      · intro q
        induction q using Quotient.inductionOn with | _ x =>
          exact ⟨circuitOf (lift S δ) (x, 0), rfl⟩)

@[simp] theorem liftCircuitEquiv_apply (δ : α → ZMod m) (hunit : UnitCarry S δ)
    (p : α × ZMod m) :
    liftCircuitEquiv S δ hunit (circuitOf (lift S δ) p) = circuitOf S p.1 := rfl

theorem lift_circuitCount (δ : α → ZMod m) (hunit : UnitCarry S δ) :
    circuitCount (lift S δ) = circuitCount S := Nat.card_congr (liftCircuitEquiv S δ hunit)

end TorusEven.Collar
