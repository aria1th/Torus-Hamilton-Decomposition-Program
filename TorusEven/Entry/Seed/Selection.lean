-- STATUS: main-path
import TorusEven.Entry.Seed.ResidualParity
import TorusEven.Entry.AnchorVoltage
import TorusEven.Collar.SelectionReindex
import TorusEven.Collar.SelectedSplit

namespace TorusEven.Entry.Seed

open Collar Incidence

variable (p : ℕ) (hp : 2 ≤ p) {m : ℕ} [NeZero m] (hm : 4 ≤ m) (heven : Even m)

@[simp] theorem labels_symm_left_fst (q : Fin 4) :
    ((labels p hp hm heven).symm (.inl q)).1 = .inl (anchorColor q) := rfl

@[simp] theorem labels_symm_right_fst (c : Shell.Color p) :
    ((labels p hp hm heven).symm (.inr c)).1 = .inr c := rfl

include hm heven in
theorem exists_blockSelection : ∃ S : BlockSelection (factorization (m := m) p hp) xChart 0 ∅,
    ∀ c : Fin 3, splitVoltage S.sources (.inl c) = anchorVoltage c := by
  classical
  obtain ⟨J, hJ, hactive⟩ := exists_matchedSelection p hp hm heven
  let e := labels p hp hm heven
  have hs (hw : ZMod m × ZMod m) :
      (support p hp heven 0 hw).map e.symm.toEmbedding =
        (factorization p hp).blockSupport xChart 0 hw := by
    rw [support_eq p hp heven hm]
    ext q
    simp only [Finset.mem_map_equiv, e, Equiv.symm_symm, Equiv.symm_apply_apply]
  let S : BlockSelection (factorization p hp) xChart 0 ∅ :=
    ⟨fun hw t => (J hw t).map e.symm.toEmbedding, by
      simpa only [funext hs, Finset.map_empty,
        MultitorusFactorization.activeColumns, Finset.notMem_empty, Finset.filter_false]
        using hJ.map e.symm⟩
  refine ⟨S, fun c => ?_⟩
  funext x
  have hmem : Sum.inl c ∈ S.sources x ↔ ∃ q : Fin 4, anchorColor q = c ∧ anchor q = x := by
    change Sum.inl c ∈ ((J (xChart.symm x).1 (xChart.symm x).2).map e.symm.toEmbedding).image
      Sigma.fst ↔ _
    constructor
    · intro h
      obtain ⟨l, hl, he⟩ := Finset.mem_image.mp h
      obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hl
      cases q with
      | inl q =>
        have hc : anchorColor q = c := Sum.inl.inj he
        have hx : x = anchor q := by
          simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using (hactive _ _ q).mp hq
        exact ⟨q, hc, hx.symm⟩
      | inr d =>
        change Sum.inr d = (Sum.inl c : Color p) at he
        exact (Sum.inr_ne_inl he).elim
    · rintro ⟨q, hc, hx⟩
      refine Finset.mem_image.mpr ⟨e.symm (.inl q), ?_, ?_⟩
      · apply Finset.mem_map.mpr
        refine ⟨.inl q, (hactive _ _ q).mpr ?_, rfl⟩
        simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using hx.symm
      · exact congrArg Sum.inl hc
  simp only [splitVoltage, anchorVoltage, hmem]

end TorusEven.Entry.Seed
