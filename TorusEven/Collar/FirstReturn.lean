-- STATUS: main-path
import TorusEven.D5.FirstReturn

namespace TorusEven.Surgery

open Function

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (S : Equiv.Perm α) (U : Set α) [DecidablePred (· ∈ U)]

def openGap (u : α) : Set α :=
  {x | ∃ k, 0 < k ∧ k < retTime S U u ∧ S^[k] u = x}

theorem openGap_not_mem {u x : α} (hu : u ∈ U) (hx : x ∈ openGap S U u) : x ∉ U := by
  obtain ⟨k, hk, hkt, rfl⟩ := hx
  exact not_mem_of_lt_retTime S U hu hk hkt

theorem retTime_eq_of_first {u : α} (hu : u ∈ U) {n : ℕ}
    (hn : 0 < n) (hret : S^[n] u ∈ U)
    (hfirst : ∀ k, 0 < k → k < n → S^[k] u ∉ U) : retTime S U u = n := by
  apply le_antisymm
  · unfold retTime
    rw [dif_pos hu]
    exact Nat.find_le ⟨hn, hret⟩
  · by_contra h
    exact hfirst _ (retTime_pos S U hu) (by omega) (ret_mem S U hu)

theorem segment_indices_eq {u v : α} (hu : u ∈ U) (hv : v ∈ U)
    {j k : ℕ} (hj : 0 < j) (hju : j ≤ retTime S U u)
    (hk : 0 < k) (hkv : k ≤ retTime S U v) (heq : S^[j] u = S^[k] v) :
    u = v ∧ j = k := by
  rcases lt_trichotomy j k with hlt | rfl | hlt
  · have h : u = S^[k - j] v := by
      apply S.injective.iterate j
      rw [← Function.iterate_add_apply]
      simpa only [show j + (k - j) = k by omega] using heq
    exact False.elim (not_mem_of_lt_retTime S U hv (by omega) (by omega) (h ▸ hu))
  · exact ⟨S.injective.iterate j heq, rfl⟩
  · have h : v = S^[j - k] u := by
      apply S.injective.iterate k
      rw [← Function.iterate_add_apply]
      simpa only [show k + (j - k) = j by omega] using heq.symm
    exact False.elim (not_mem_of_lt_retTime S U hu (by omega) (by omega) (h ▸ hv))

theorem openGap_disjoint {u v : α} (hu : u ∈ U) (hv : v ∈ U) (hne : u ≠ v) :
    Disjoint (openGap S U u) (openGap S U v) := by
  rw [Set.disjoint_left]
  rintro x ⟨j, hj, hju, hjx⟩ ⟨k, hk, hkv, hkx⟩
  exact hne (segment_indices_eq S U hu hv hj hju.le hk hkv.le (hjx.trans hkx.symm)).1

theorem ret_injective : Function.Injective (fun u : U => (⟨ret S U u, ret_mem S U u.2⟩ : U)) := by
  intro u v h
  apply Subtype.ext
  exact (segment_indices_eq S U u.2 v.2
    (retTime_pos S U u.2) le_rfl (retTime_pos S U v.2) le_rfl
    (congrArg Subtype.val h)).1

noncomputable def retPerm : Equiv.Perm U :=
  Equiv.ofBijective (fun u => ⟨ret S U u, ret_mem S U u.2⟩)
    ⟨ret_injective S U, Finite.surjective_of_injective (ret_injective S U)⟩

@[simp] theorem retPerm_apply (u : U) : (retPerm S U u).val = ret S U u := rfl

noncomputable def segmentEquiv (hmeet : ∀ x, ∃ w ∈ U, w ∈ orbitSet S x) :
    (Σ u : U, Fin (retTime S U u)) ≃ α :=
  Equiv.ofBijective (fun q => S^[q.2.val + 1] q.1.val) (by
    constructor
    · rintro ⟨⟨u, hu⟩, j⟩ ⟨⟨v, hv⟩, k⟩ heq
      obtain ⟨huv, hjk⟩ := segment_indices_eq S U hu hv (by omega) j.isLt
        (by omega) k.isLt heq
      subst v
      have : j = k := Fin.ext (by omega)
      subst k
      rfl
    · intro x
      have hx : x ∈ ⋃ w ∈ U, seg S U w := by
        rw [iUnion_seg_eq_univ S U hmeet]
        trivial
      obtain ⟨w, hw, k, hk, hkt, hkx⟩ := Set.mem_iUnion₂.mp hx
      refine ⟨⟨⟨w, hw⟩, ⟨k - 1, by change k - 1 < retTime S U w; omega⟩⟩, ?_⟩
      dsimp only
      simpa only [show k - 1 + 1 = k by omega] using hkx)

theorem sum_retTime (hmeet : ∀ x, ∃ w ∈ U, w ∈ orbitSet S x) :
    ∑ u : U, retTime S U u = Fintype.card α := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using
    Fintype.card_congr (segmentEquiv S U hmeet)

variable {β : Type*} [Fintype β] [DecidableEq β]

theorem retTime_semiconj (T : Equiv.Perm β) (V : Set β) [DecidablePred (· ∈ V)]
    (f : α → β) (hf : Semiconj f S T) (hU : ∀ x, x ∈ U ↔ f x ∈ V)
    {u : α} (hu : u ∈ U) : retTime T V (f u) = retTime S U u := by
  apply retTime_eq_of_first T V ((hU u).mp hu) (retTime_pos S U hu)
  · rw [← hf.iterate_right]
    exact (hU _).mp (ret_mem S U hu)
  · intro k hk hkt
    rw [← hf.iterate_right]
    exact fun h => not_mem_of_lt_retTime S U hu hk hkt ((hU _).mpr h)

theorem ret_semiconj (T : Equiv.Perm β) (V : Set β) [DecidablePred (· ∈ V)]
    (f : α → β) (hf : Semiconj f S T) (hU : ∀ x, x ∈ U ↔ f x ∈ V)
    {u : α} (hu : u ∈ U) : f (ret S U u) = ret T V (f u) := by
  unfold ret
  rw [retTime_semiconj S U T V f hf hU hu, hf.iterate_right]

theorem openGap_map (T : Equiv.Perm β) (V : Set β) [DecidablePred (· ∈ V)]
    (f : α → β) (hf : Semiconj f S T) (hU : ∀ x, x ∈ U ↔ f x ∈ V)
    {u x : α} (hu : u ∈ U) (hx : x ∈ openGap S U u) : f x ∈ openGap T V (f u) := by
  obtain ⟨k, hk, hkt, rfl⟩ := hx
  exact ⟨k, hk, by rwa [retTime_semiconj S U T V f hf hU hu],
    (hf.iterate_right k u).symm⟩

omit [Fintype α] [DecidableEq α] in
theorem eq_of_bijective_except {β : Type*} (f g : α → β) (hf : Function.Bijective f)
    (hg : Function.Injective g) (u : α) (h : ∀ x, x ≠ u → f x = g x) : f = g := by
  funext x
  by_cases hx : x = u
  · subst x
    obtain ⟨v, hv⟩ := hf.2 (g u)
    by_cases hvu : v = u
    · simpa only [hvu] using hv
    · exact False.elim (hvu (hg ((h v hvu).symm.trans hv)))
  · exact h x hx

end TorusEven.Surgery
