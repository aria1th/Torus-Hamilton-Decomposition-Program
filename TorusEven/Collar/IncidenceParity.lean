-- STATUS: main-path
import TorusEven.Collar.Incidence

namespace TorusEven.Collar.Incidence

variable {B R Ω : Type*} [Fintype B] [Fintype R] [Nonempty R] [Finite Ω] [DecidableEq Ω]

theorem evenComponents_of_coherent_odd_columns (J : B → R → Finset Ω)
    (hne : ∀ p : B × R, (J p.1 p.2).Nonempty) (hc : ∀ b, Coherent (J b))
    (w : B → ℕ) (hw : ∀ b r, (J b r).card = w b) (hR : Even (Fintype.card R))
    (hcol : ∀ x, Odd ((Finset.univ.filter (fun p : B × R => x ∈ J p.1 p.2)).card)) :
    EvenComponents (fun p : B × R => J p.1 p.2) := by
  classical
  letI := Fintype.ofFinite Ω
  let A : B × R → Finset Ω := fun p => J p.1 p.2
  let r₀ : R := Classical.choice ‹Nonempty R›
  let k : B → Component A := fun b => blockComponent A hne (b, r₀)
  have hcomp (b : B) (r : R) (x : Ω) (hx : x ∈ J b r) : componentOf A x = k b :=
    (component_eq_block A hne hx).trans (coherent_blockComponent J hne hc b r r₀)
  let M : B → R → Ω → ZMod 2 := fun b r x => if x ∈ J b r then 1 else 0
  have hdegree (x : Ω) : (∑ b, ∑ r, M b r x) = 1 := by
    have h := (hcol x).natCast_zmod_two
    simpa only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter,
      Fintype.sum_prod_type, M, apply_ite, Nat.cast_one, Nat.cast_zero] using h
  have hrow (b : B) (r : R) : (∑ x, M b r x) = (w b : ZMod 2) := by
    have h := congrArg (fun n : ℕ => (n : ZMod 2)) (hw b r)
    simpa only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter,
      M, Finset.sum_ite_mem, Finset.univ_inter] using h
  intro q
  let v : Ω → ZMod 2 := fun x => if componentOf A x = q then 1 else 0
  let z : B → ZMod 2 := fun b => if k b = q then 1 else 0
  have hmask (b : B) (r : R) (x : Ω) : v x * M b r x = z b * M b r x := by
    by_cases hx : x ∈ J b r
    · simp only [v, z, M, if_pos hx, hcomp b r x hx]
    · simp only [M, if_neg hx, mul_zero]
  apply ZMod.natCast_eq_zero_iff_even.mp
  have hcard : (Nat.card {x // componentOf A x = q} : ZMod 2) = ∑ x, v x := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_eq_sum_ones,
      Nat.cast_sum, Nat.cast_one, Finset.sum_filter, v, apply_ite, Nat.cast_zero]
  rw [hcard]
  calc
    (∑ x, v x) = ∑ x, v x * (∑ b, ∑ r, M b r x) := by simp only [hdegree, mul_one]
    _ = ∑ b, ∑ r, ∑ x, v x * M b r x := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ r : R, z b * (w b : ZMod 2) := by
      simp only [hmask, ← Finset.mul_sum, hrow]
    _ = 0 := by simp [hR.natCast_zmod_two]

theorem odd_of_unit_mod_even {m n : ℕ} (hm : Even m) (hn : IsUnit (n : ZMod m)) : Odd n :=
  ((ZMod.isUnit_iff_coprime n m).mp hn).of_dvd_right hm.two_dvd |>.odd_of_right

omit [Nonempty R] [Finite Ω] in
theorem odd_complement_columns (A : B → Finset Ω) (J : B → R → Finset Ω)
    (hJ : ∀ b r, J b r ⊆ A b) (hR : Even (Fintype.card R))
    (hcol : ∀ x, Odd ((Finset.univ.filter (fun p : B × R => x ∈ J p.1 p.2)).card)) :
    ∀ x, Odd ((Finset.univ.filter (fun p : B × R => x ∈ A p.1 \ J p.1 p.2)).card) := by
  classical
  intro x
  have hsum : (((Finset.univ.filter (fun p : B × R => x ∈ J p.1 p.2)).card : ZMod 2) +
      (Finset.univ.filter (fun p : B × R => x ∈ A p.1 \ J p.1 p.2)).card) = 0 := by
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter,
      Fintype.sum_prod_type, apply_ite, Nat.cast_zero]
    rw [← Finset.sum_add_distrib]
    have hentry (b : B) (r : R) :
        (if x ∈ J b r then (1 : ZMod 2) else 0) +
          (if x ∈ A b \ J b r then 1 else 0) = if x ∈ A b then 1 else 0 := by
      by_cases hx : x ∈ J b r
      · simp [hx, hJ b r hx]
      · simp [hx]
    simp only [← Finset.sum_add_distrib, hentry]
    simp [hR.natCast_zmod_two]
  apply ZMod.natCast_eq_one_iff_odd.mp
  rw [(hcol x).natCast_zmod_two] at hsum
  exact (eq_neg_of_add_eq_zero_right hsum).trans (by decide)

end TorusEven.Collar.Incidence
