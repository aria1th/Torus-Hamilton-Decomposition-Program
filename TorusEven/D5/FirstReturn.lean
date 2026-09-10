-- STATUS: main-path (F1: first return, source surgery in orbit form)
import Mathlib
import Shared.ReturnLift

/-!
# First return and source surgery (manuscript Lemma `lem:surgery`, orbit form)

For a permutation `S` of a finite type, a marked set `U`, and a permutation `r` supported
on `U`, the orbits of `S ∘ r` are unions of `S`-segments between consecutive visits to `U`,
indexed by the orbits of `ret ∘ r` on `U`, where `ret` is the first return of `S` to `U`.
-/

namespace TorusEven
namespace Surgery

open Function

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Forward orbit of `x`. -/
def orbitSet (f : α → α) (x : α) : Set α := Set.range fun n : ℕ => f^[n] x

theorem mem_orbitSet_iff {f : α → α} {x y : α} : y ∈ orbitSet f x ↔ ∃ n, f^[n] x = y :=
  Iff.rfl

theorem self_mem_orbitSet (f : α → α) (x : α) : x ∈ orbitSet f x := ⟨0, rfl⟩

theorem iterate_mem_orbitSet (f : α → α) (x : α) (n : ℕ) : f^[n] x ∈ orbitSet f x := ⟨n, rfl⟩

/-- For an injective map on a finite type, orbits are symmetric. -/
theorem exists_iterate_back {f : α → α} (hf : Injective f) (x : α) (n : ℕ) :
    ∃ k, f^[k] (f^[n] x) = x := by
  obtain ⟨p, hp, hper⟩ := mem_periodicPts.1 (hf.mem_periodicPts x)
  refine ⟨p * n - n, ?_⟩
  have hnle : n ≤ p * n := Nat.le_mul_of_pos_left n hp
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hnle]
  exact (hper.mul_const n).eq

theorem orbitSet_eq_of_mem {f : α → α} (hf : Injective f) {x y : α} (hy : y ∈ orbitSet f x) :
    orbitSet f y = orbitSet f x := by
  obtain ⟨n, rfl⟩ := hy
  ext z
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k + n, by dsimp only; rw [Function.iterate_add_apply]⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨j, hj⟩ := exists_iterate_back hf x n
    exact ⟨k + j, by dsimp only; rw [Function.iterate_add_apply, hj]⟩

theorem mem_orbitSet_symm {f : α → α} (hf : Injective f) {x y : α} (hy : y ∈ orbitSet f x) :
    x ∈ orbitSet f y := by
  rw [orbitSet_eq_of_mem hf hy]
  exact self_mem_orbitSet f x

/-- A bijection whose orbit through some point is everything is a single cycle. -/
theorem single_cycle_of_orbitSet_univ {f : α → α} (hf : Bijective f) (u : α)
    (hu : orbitSet f u = Set.univ) : Shared.IsSingleCycleMap f := by
  refine ⟨hf, ?_⟩
  intro x y
  have hx : x ∈ orbitSet f u := by rw [hu]; trivial
  have hy : y ∈ orbitSet f u := by rw [hu]; trivial
  have hyx : y ∈ orbitSet f x := by
    rw [orbitSet_eq_of_mem hf.1 hx]
    exact hy
  exact hyx

variable (S : α ≃ α) (U : Set α) [DecidablePred (· ∈ U)]

theorem exists_return (w : α) (hw : w ∈ U) : ∃ n, 0 < n ∧ S^[n] w ∈ U := by
  obtain ⟨p, hp, hper⟩ := mem_periodicPts.1 (S.injective.mem_periodicPts w)
  exact ⟨p, hp, by rw [hper.eq]; exact hw⟩

/-- First return time to `U` (zero off `U`). -/
noncomputable def retTime (w : α) : ℕ :=
  if hw : w ∈ U then Nat.find (exists_return S U w hw) else 0

/-- First return map. -/
noncomputable def ret (w : α) : α := S^[retTime S U w] w

theorem retTime_pos {w : α} (hw : w ∈ U) : 0 < retTime S U w := by
  unfold retTime
  rw [dif_pos hw]
  exact (Nat.find_spec (exists_return S U w hw)).1

theorem ret_mem {w : α} (hw : w ∈ U) : ret S U w ∈ U := by
  unfold ret retTime
  rw [dif_pos hw]
  exact (Nat.find_spec (exists_return S U w hw)).2

theorem not_mem_of_lt_retTime {w : α} (hw : w ∈ U) {k : ℕ} (hk0 : 0 < k)
    (hk : k < retTime S U w) : S^[k] w ∉ U := by
  unfold retTime at hk
  rw [dif_pos hw] at hk
  intro hmem
  exact Nat.find_min (exists_return S U w hw) hk ⟨hk0, hmem⟩

/-- The `S`-segment from `S w` to the first return of `w`. -/
def seg (w : α) : Set α := {y | ∃ k, 1 ≤ k ∧ k ≤ retTime S U w ∧ S^[k] w = y}

/-! ### Surgery with a permutation supported on `U` -/

variable (r : α → α)

/-- The return map after surgery, on `U`. -/
noncomputable def afterRet (v : α) : α := ret S U (r v)

theorem iterate_comp_eq (hsupp : ∀ x, x ∉ U → r x = x) (hmaps : ∀ x, x ∈ U → r x ∈ U)
    {v : α} (hv : v ∈ U) :
    ∀ k, 1 ≤ k → k ≤ retTime S U (r v) → (S ∘ r)^[k] v = S^[k] (r v) := by
  intro k hk1 hkle
  induction k with
  | zero => omega
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        simp
      · have := ih hkpos (by omega)
        rw [Function.iterate_succ_apply', this, Function.iterate_succ_apply']
        simp only [Function.comp]
        congr 1
        apply hsupp
        exact not_mem_of_lt_retTime S U (hmaps v hv) hkpos (by omega)

theorem iterate_comp_retTime (hsupp : ∀ x, x ∉ U → r x = x) (hmaps : ∀ x, x ∈ U → r x ∈ U)
    {v : α} (hv : v ∈ U) :
    (S ∘ r)^[retTime S U (r v)] v = afterRet S U r v := by
  unfold afterRet ret
  exact iterate_comp_eq S U r hsupp hmaps hv _ (retTime_pos S U (hmaps v hv)) le_rfl

theorem afterRet_mem (hmaps : ∀ x, x ∈ U → r x ∈ U) {v : α} (hv : v ∈ U) :
    afterRet S U r v ∈ U :=
  ret_mem S U (hmaps v hv)

theorem afterRet_iterate_mem (hmaps : ∀ x, x ∈ U → r x ∈ U) {u : α} (hu : u ∈ U) (j : ℕ) :
    (afterRet S U r)^[j] u ∈ U := by
  induction j with
  | zero => simpa
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact afterRet_mem S U r hmaps ih

theorem exists_iterate_comp_eq_afterRet_iterate (hsupp : ∀ x, x ∉ U → r x = x)
    (hmaps : ∀ x, x ∈ U → r x ∈ U) {u : α} (hu : u ∈ U) (j : ℕ) :
    ∃ N, (S ∘ r)^[N] u = (afterRet S U r)^[j] u := by
  induction j with
  | zero => exact ⟨0, rfl⟩
  | succ j ih =>
      obtain ⟨N, hN⟩ := ih
      refine ⟨retTime S U (r ((afterRet S U r)^[j] u)) + N, ?_⟩
      rw [Function.iterate_add_apply, hN, Function.iterate_succ_apply']
      exact iterate_comp_retTime S U r hsupp hmaps (afterRet_iterate_mem S U r hmaps hu j)

/-- Orbits of `S ∘ r` through a marked point are unions of segments indexed by the orbit
of the return map after surgery. -/
theorem orbitSet_comp_eq (hsupp : ∀ x, x ∉ U → r x = x) (hmaps : ∀ x, x ∈ U → r x ∈ U)
    (hr : Bijective r) {u : α} (hu : u ∈ U) :
    orbitSet (S ∘ r) u = ⋃ v ∈ orbitSet (afterRet S U r) u, seg S U (r v) := by
  have hSr : Bijective (S ∘ r) := S.bijective.comp hr
  ext y
  constructor
  · rintro ⟨n, rfl⟩
    -- reduce to `n ≥ 1` using periodicity of `u`
    suffices h : ∀ n, 1 ≤ n → (S ∘ r)^[n] u ∈ ⋃ v ∈ orbitSet (afterRet S U r) u, seg S U (r v) by
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        obtain ⟨p, hp, hper⟩ := mem_periodicPts.1 (hSr.1.mem_periodicPts u)
        have := h p hp
        rwa [hper.eq] at this
      · exact h n hnpos
    intro n hn1
    induction n with
    | zero => omega
    | succ n ih =>
        -- invariant: `(S ∘ r)^[n+1] u = S^[k] (r v)` with `v` in the orbit, `1 ≤ k ≤ τ (r v)`
        suffices key : ∀ n, 1 ≤ n → ∃ v, v ∈ orbitSet (afterRet S U r) u ∧
            ∃ k, 1 ≤ k ∧ k ≤ retTime S U (r v) ∧ (S ∘ r)^[n] u = S^[k] (r v) by
          obtain ⟨v, hv, k, hk1, hkle, hk⟩ := key (n + 1) hn1
          exact Set.mem_biUnion hv ⟨k, hk1, hkle, hk.symm⟩
        intro n hn1
        induction n with
        | zero => omega
        | succ n ih2 =>
            rcases Nat.eq_zero_or_pos n with hn0 | hnpos
            · subst hn0
              refine ⟨u, self_mem_orbitSet _ u, 1, le_rfl, retTime_pos S U (hmaps u hu), ?_⟩
              simp
            · obtain ⟨v, hv, k, hk1, hkle, hk⟩ := ih2 hnpos
              have hvU : v ∈ U := by
                obtain ⟨j, rfl⟩ := hv
                exact afterRet_iterate_mem S U r hmaps hu j
              rcases lt_or_eq_of_le hkle with hlt | heq
              · refine ⟨v, hv, k + 1, by omega, hlt, ?_⟩
                rw [Function.iterate_succ_apply', hk, Function.iterate_succ_apply']
                simp only [Function.comp]
                congr 1
                exact hsupp _ (not_mem_of_lt_retTime S U (hmaps v hvU) (by omega) hlt)
              · -- we are at the return point `afterRet v`; start the next segment
                have hret : (S ∘ r)^[n] u = afterRet S U r v := by
                  rw [hk, heq]
                  rfl
                refine ⟨afterRet S U r v, ?_, 1, le_rfl,
                  retTime_pos S U (hmaps _ (afterRet_mem S U r hmaps hvU)), ?_⟩
                · obtain ⟨j, rfl⟩ := hv
                  exact ⟨j + 1, by dsimp only; rw [Function.iterate_succ_apply']⟩
                · rw [Function.iterate_succ_apply', hret]
                  simp
  · intro hy
    obtain ⟨v, hv, k, hk1, hkle, rfl⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨j, rfl⟩ := hv
    obtain ⟨N, hN⟩ := exists_iterate_comp_eq_afterRet_iterate S U r hsupp hmaps hu j
    refine ⟨k + N, ?_⟩
    dsimp only
    rw [Function.iterate_add_apply, hN]
    exact iterate_comp_eq S U r hsupp hmaps (afterRet_iterate_mem S U r hmaps hu j) k hk1 hkle

/-! ### Consequences -/

/-- If the orbit of `w` meets `U` only at `w`, the return time is the period. -/
theorem retTime_eq_minimalPeriod_of_unique {w : α} (hw : w ∈ U)
    (huniq : ∀ y ∈ orbitSet S w, y ∈ U → y = w) :
    retTime S U w = Function.minimalPeriod S w := by
  apply le_antisymm
  · have hpos := minimalPeriod_pos_of_mem_periodicPts (S.injective.mem_periodicPts w)
    unfold retTime
    rw [dif_pos hw]
    exact Nat.find_le ⟨hpos, by rw [iterate_minimalPeriod]; exact hw⟩
  · by_contra hlt
    push_neg at hlt
    have hmem : S^[retTime S U w] w ∈ U := ret_mem S U hw
    have heq : S^[retTime S U w] w = w :=
      huniq _ (iterate_mem_orbitSet S w _) hmem
    have hpos := retTime_pos S U hw
    exact absurd (IsPeriodicPt.minimalPeriod_le hpos heq) (not_le.2 hlt)

theorem ret_eq_self_of_unique {w : α} (hw : w ∈ U)
    (huniq : ∀ y ∈ orbitSet S w, y ∈ U → y = w) : ret S U w = w := by
  unfold ret
  rw [retTime_eq_minimalPeriod_of_unique S U hw huniq, iterate_minimalPeriod]

/-- If the orbit of `w` meets `U` only at `w`, its segment is the whole `S`-orbit. -/
theorem seg_eq_orbitSet_of_unique {w : α} (hw : w ∈ U)
    (huniq : ∀ y ∈ orbitSet S w, y ∈ U → y = w) :
    seg S U w = orbitSet S w := by
  have hper := retTime_eq_minimalPeriod_of_unique S U hw huniq
  ext y
  constructor
  · rintro ⟨k, _, _, rfl⟩
    exact iterate_mem_orbitSet S w k
  · rintro ⟨n, rfl⟩
    have hpos := minimalPeriod_pos_of_mem_periodicPts (S.injective.mem_periodicPts w)
    show ∃ k, 1 ≤ k ∧ k ≤ retTime S U w ∧ S^[k] w = S^[n] w
    rw [hper]
    by_cases h0 : n % Function.minimalPeriod S w = 0
    · refine ⟨Function.minimalPeriod S w, hpos, le_rfl, ?_⟩
      rw [iterate_minimalPeriod, ← iterate_mod_minimalPeriod_eq, h0]
      rfl
    · exact ⟨n % Function.minimalPeriod S w, Nat.pos_of_ne_zero h0, (Nat.mod_lt _ hpos).le,
        iterate_mod_minimalPeriod_eq⟩

end Surgery
end TorusEven
