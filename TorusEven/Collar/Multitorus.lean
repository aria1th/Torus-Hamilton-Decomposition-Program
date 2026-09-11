-- STATUS: main-path
import Shared.TorusCayley
import Mathlib

namespace TorusEven.Collar

variable (C I : Type*) [Fintype C] [DecidableEq I] (m : ℕ)

structure MultitorusFactorization where
  width : I → ℕ
  width_pos : ∀ i, 0 < width i
  direction : C → (I → ZMod m) → I
  step : C → Equiv.Perm (I → ZMod m)
  step_eq : ∀ c x j, step c x j = x j + if j = direction c x then 1 else 0
  quota : ∀ x i, (Finset.univ.filter (fun c => direction c x = i)).card = width i

variable {C I m}

def MultitorusFactorization.users (F : MultitorusFactorization C I m)
    (x : I → ZMod m) (i : I) : Finset C := Finset.univ.filter (fun c => F.direction c x = i)

def MultitorusFactorization.ActiveSeparated (F : MultitorusFactorization C I m)
    (active : Set C) : Prop := ∀ x, Set.InjOn (fun c => F.direction c x) active

@[simp] theorem MultitorusFactorization.mem_users (F : MultitorusFactorization C I m)
    (x : I → ZMod m) (i : I) (c : C) : c ∈ F.users x i ↔ F.direction c x = i := by
  simp [users]

@[simp] theorem MultitorusFactorization.card_users (F : MultitorusFactorization C I m)
    (x : I → ZMod m) (i : I) : (F.users x i).card = F.width i := F.quota x i

theorem MultitorusFactorization.sum_width [Fintype I] (F : MultitorusFactorization C I m) :
    ∑ i, F.width i = Fintype.card C := by
  let x : I → ZMod m := 0
  simp_rw [← F.quota x, Finset.card_eq_sum_ones]
  rw [Finset.sum_fiberwise_of_maps_to (fun c _ => Finset.mem_univ (F.direction c x))]
  simp

def MultitorusFactorization.excess [Fintype I] (F : MultitorusFactorization C I m) : ℕ :=
  ∑ i, (F.width i - 1)

theorem MultitorusFactorization.excess_add_card [Fintype I]
    (F : MultitorusFactorization C I m) : F.excess + Fintype.card I = Fintype.card C := by
  calc
    F.excess + Fintype.card I = ∑ i, ((F.width i - 1) + 1) := by
      simp [excess, Finset.sum_add_distrib]
    _ = ∑ i, F.width i := Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (F.width_pos i))
    _ = Fintype.card C := F.sum_width

theorem MultitorusFactorization.excess_eq [Fintype I] (F : MultitorusFactorization C I m) :
    F.excess = Fintype.card C - Fintype.card I := by have := F.excess_add_card; omega

theorem MultitorusFactorization.excess_zero_iff [Fintype I] (F : MultitorusFactorization C I m) :
    F.excess = 0 ↔ ∀ i, F.width i = 1 := by
  constructor
  · intro h i
    have hi : F.width i - 1 ≤ F.excess :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (F.width j - 1)) (Finset.mem_univ i)
    have := F.width_pos i
    omega
  · intro h
    simp [excess, h]

variable {K : Type*} [DecidableEq K]

def coordinateEquiv (e : I ≃ K) : (I → ZMod m) ≃ (K → ZMod m) :=
  Equiv.arrowCongr e (Equiv.refl _)

def MultitorusFactorization.reindex (F : MultitorusFactorization C I m) (e : I ≃ K) :
    MultitorusFactorization C K m where
  width k := F.width (e.symm k)
  width_pos k := F.width_pos (e.symm k)
  direction c x := e (F.direction c ((coordinateEquiv e).symm x))
  step c := (coordinateEquiv e).symm.trans ((F.step c).trans (coordinateEquiv e))
  step_eq c x k := by
    change F.step c (fun i => x (e i)) (e.symm k) =
      x k + if k = e (F.direction c (fun i => x (e i))) then 1 else 0
    rw [F.step_eq]
    simp only [e.apply_symm_apply, e.symm_apply_eq]
  quota x k := by
    simp only [Equiv.apply_eq_iff_eq_symm_apply]
    exact F.quota ((coordinateEquiv e).symm x) (e.symm k)

theorem MultitorusFactorization.reindex_singleCycle (F : MultitorusFactorization C I m)
    (e : I ≃ K) (c : C) (h : Shared.IsSingleCycleMap (F.step c)) :
    Shared.IsSingleCycleMap ((F.reindex e).step c) := by
  let E := coordinateEquiv (m := m) e
  have he : Function.Semiconj E (F.step c) ((F.reindex e).step c) := by
    intro x
    simp [reindex, E]
  refine ⟨((F.reindex e).step c).bijective, ?_⟩
  intro x y
  obtain ⟨n, hn⟩ := h.2 (E.symm x) (E.symm y)
  refine ⟨n, ?_⟩
  simpa only [E.apply_symm_apply] using
    (he.iterate_right n (E.symm x)).symm.trans (congrArg E hn)

def MultitorusFactorization.toCayley {d : ℕ} (F : MultitorusFactorization (Fin d) (Fin d) m)
    (hw : ∀ i, F.width i = 1) (hH : ∀ c, Shared.IsSingleCycleMap (F.step c)) :
    Shared.CayleyDecomposition d m where
  colorDir := F.direction
  edgePartition := by
    intro x i
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp ((F.quota x i).trans (hw i))
    have hmem : ∀ c', F.direction c' x = i ↔ c' = c := by
      intro c'
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        using (show c' ∈ Finset.univ.filter (fun c => F.direction c x = i) ↔
          c' ∈ ({c} : Finset (Fin d)) by rw [hc])
    exact ⟨c, (hmem c).mpr rfl, fun c' hc' => (hmem c').mp hc'⟩
  colorHamiltonian := by
    intro c
    have hstep : Shared.cayleyColorStep F.direction c = F.step c := by
      funext x j
      exact (F.step_eq c x j).symm
    rw [hstep]
    exact hH c

noncomputable def MultitorusFactorization.toCayleyOfUnitWidths {d : ℕ} [Fintype I]
    (F : MultitorusFactorization (Fin d) I m) (hw : ∀ i, F.width i = 1)
    (hH : ∀ c, Shared.IsSingleCycleMap (F.step c)) : Shared.CayleyDecomposition d m := by
  have hi : Fintype.card I = d := by simpa [hw] using F.sum_width
  let e : I ≃ Fin d := Fintype.equivFinOfCardEq hi
  exact (F.reindex e).toCayley (fun k => hw (e.symm k))
    (fun c => F.reindex_singleCycle e c (hH c))

end TorusEven.Collar
