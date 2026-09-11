-- STATUS: main-path
import TorusEven.Collar.PinnedSelection
import TorusEven.Collar.ComponentPairs

namespace TorusEven.Collar.Incidence

variable {B Ω Ω' : Type*} [Fintype B] [DecidableEq Ω] [DecidableEq Ω']
variable {m : ℕ} [NeZero m] {A : B → Finset Ω} {active : Finset Ω}
variable {J : B → ZMod m → Finset Ω}

theorem IsPinnedSelection.map (h : IsPinnedSelection A active J) (e : Ω ≃ Ω') :
    IsPinnedSelection (fun b => (A b).map e.toEmbedding) (active.map e.toEmbedding)
      (fun b t => (J b t).map e.toEmbedding) := by
  refine ⟨fun b t => Finset.map_subset_map.mpr (h.subset b t), ?_, ?_, ?_, ?_, ?_⟩
  · intro b t
    simpa only [Finset.card_map] using h.card b t
  · intro x
    simpa only [Finset.mem_map_equiv] using h.residues (e.symm x)
  · intro b
    exact (Finset.disjoint_map e.toEmbedding).mpr (h.pinned b)
  · intro b hb
    apply coherent_of_map_subset (J b) _ e
      (fun _ x hx => Finset.mem_map.mpr ⟨x, hx, rfl⟩)
    exact h.selected_coherent b (by simpa only [Finset.card_map] using hb)
  · intro b hb
    simp only [← Finset.map_sdiff]
    apply coherent_of_map_subset (fun t => A b \ J b t) _ e
      (fun _ x hx => Finset.mem_map.mpr ⟨x, hx, rfl⟩)
    exact h.complement_coherent b (by simpa only [Finset.card_map] using hb)

end TorusEven.Collar.Incidence
