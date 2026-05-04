import Shared.ReturnLift

namespace Shared

theorem iterate_rank_add_one
    {α : Type*} {N : Nat} [NeZero N] (f : α → α) (rank : α → ZMod N)
    (hstep : ∀ x : α, rank (f x) = rank x + 1) :
    ∀ n : Nat, ∀ x : α, rank (f^[n] x) = rank x + (n : ZMod N)
  | 0, x => by simp
  | n + 1, x => by
      rw [Function.iterate_succ_apply]
      calc
        rank ((f^[n]) (f x)) = rank (f x) + (n : ZMod N) :=
          iterate_rank_add_one f rank hstep n (f x)
        _ = (rank x + 1) + (n : ZMod N) := by
          rw [hstep x]
        _ = rank x + ((n + 1 : Nat) : ZMod N) := by
          simp [Nat.cast_add, Nat.cast_one]
          ring

theorem single_cycle_of_zmod_rank
    {α : Type*} {N : Nat} [NeZero N] (f : α → α) (rank : α → ZMod N)
    (hrank : Function.Bijective rank)
    (hstep : ∀ x : α, rank (f x) = rank x + 1) :
    IsSingleCycleMap f := by
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply hrank.1
    have h : rank x + (1 : ZMod N) = rank y + 1 := by
      simpa [hstep x, hstep y] using congrArg rank hxy
    exact add_right_cancel h
  have hf_surj : Function.Surjective f := by
    intro y
    let target : ZMod N := rank y - 1
    rcases hrank.2 target with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply hrank.1
    calc
      rank (f x) = rank x + 1 := hstep x
      _ = target + 1 := by rw [hx]
      _ = rank y := by
        simp [target]
  refine ⟨⟨hf_inj, hf_surj⟩, ?_⟩
  intro x y
  rcases ZMod.natCast_zmod_surjective (rank y - rank x) with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  apply hrank.1
  calc
    rank (f^[n] x) = rank x + (n : ZMod N) :=
      iterate_rank_add_one f rank hstep n x
    _ = rank x + (rank y - rank x) := by rw [hn]
    _ = rank y := by ring

theorem single_cycle_of_zmod_rank_equiv
    {α : Type*} {N : Nat} [NeZero N] (f : α → α)
    (rank : α ≃ ZMod N)
    (hstep : ∀ x : α, rank (f x) = rank x + 1) :
    IsSingleCycleMap f :=
  single_cycle_of_zmod_rank f rank (Equiv.bijective rank) hstep

theorem zmod_rank_iterate_period
    {α : Type*} {N : Nat} [NeZero N] (f : α → α)
    (rank : α ≃ ZMod N)
    (hstep : ∀ x : α, rank (f x) = rank x + 1)
    (x : α) :
    (f^[N]) x = x := by
  apply rank.injective
  calc
    rank ((f^[N]) x) = rank x + (N : ZMod N) :=
      iterate_rank_add_one f rank hstep N x
    _ = rank x := by simp

theorem zmod_rank_orbit_cover_lt
    {α : Type*} {N : Nat} [NeZero N] (f : α → α)
    (rank : α ≃ ZMod N)
    (hstep : ∀ x : α, rank (f x) = rank x + 1)
    (base : α) :
    ∀ x : α, ∃ k : Nat, k < N ∧ (f^[k]) base = x := by
  intro x
  let delta : ZMod N := rank x - rank base
  refine ⟨delta.val, delta.val_lt, ?_⟩
  apply rank.injective
  calc
    rank ((f^[delta.val]) base) = rank base + (delta.val : ZMod N) :=
      iterate_rank_add_one f rank hstep delta.val base
    _ = rank base + delta := by rw [ZMod.natCast_zmod_val]
    _ = rank x := by
      simp [delta]

theorem zmod_add_single_cycle_of_coprime
    {m a : Nat} [NeZero m] (ha : Nat.Coprime a m) :
    IsSingleCycleMap (fun x : ZMod m => x + (a : ZMod m)) := by
  let u : (ZMod m)ˣ := ZMod.unitOfCoprime a ha
  refine single_cycle_of_zmod_rank
    (f := fun x : ZMod m => x + (a : ZMod m))
    (rank := fun x : ZMod m => (u⁻¹ : ZMod m) * x)
    ?_ ?_
  · exact Equiv.bijective (Units.mulLeft u⁻¹)
  · intro x
    have hu : (u : ZMod m) = (a : ZMod m) := by
      exact ZMod.coe_unitOfCoprime a ha
    calc
      (u⁻¹ : ZMod m) * (x + (a : ZMod m)) =
          (u⁻¹ : ZMod m) * x + (u⁻¹ : ZMod m) * (a : ZMod m) := by ring
      _ = (u⁻¹ : ZMod m) * x + (u⁻¹ : ZMod m) * (u : ZMod m) := by rw [hu]
      _ = (u⁻¹ : ZMod m) * x + 1 := by simp

theorem zmod_add_single_cycle_of_unit
    {m : Nat} [NeZero m] {a : ZMod m} (ha : IsUnit a) :
    IsSingleCycleMap (fun x : ZMod m => x + a) := by
  let u : (ZMod m)ˣ := ha.unit
  refine single_cycle_of_zmod_rank
    (f := fun x : ZMod m => x + a)
    (rank := Units.mulLeft u⁻¹)
    ?_ ?_
  · exact Equiv.bijective (Units.mulLeft u⁻¹)
  · intro x
    have hu : (u : ZMod m) = a := ha.unit_spec
    change (↑(u⁻¹) : ZMod m) * (x + a) =
      (↑(u⁻¹) : ZMod m) * x + 1
    calc
      (↑(u⁻¹) : ZMod m) * (x + a) =
          (↑(u⁻¹) : ZMod m) * x + (↑(u⁻¹) : ZMod m) * a := by ring
      _ = (↑(u⁻¹) : ZMod m) * x + (↑(u⁻¹) : ZMod m) * (u : ZMod m) := by rw [hu]
      _ = (↑(u⁻¹) : ZMod m) * x + 1 := by simp

end Shared
