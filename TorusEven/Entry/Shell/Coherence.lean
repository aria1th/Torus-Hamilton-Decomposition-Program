-- STATUS: main-path
import TorusEven.Entry.Shell.Rows

namespace TorusEven.Entry.Shell

open Collar

variable (p : ℕ) (hp : 2 ≤ p) {m : ℕ} (hm : 4 ≤ m)
include hm

theorem pair_row_coherent (h : ℕ) (F : Finset (Color p)) (side : Bool)
    (hsize : 2 ≤ F.card + (pairs p hp h).count) :
    Incidence.Coherent ((pairs p hp h).row (event (m := m)) F side) := by
  have h10 : (1 : ZMod m) ≠ 0 := by
    simpa using cast_ne_zero (m := m) (n := 1) (by omega) (by omega)
  have h20 : (2 : ZMod m) ≠ 0 := by
    simpa using cast_ne_zero (m := m) (n := 2) (by omega) (by omega)
  have h21 : (2 : ZMod m) ≠ 1 := by intro he; apply h10; linear_combination he
  apply (pairs p hp h).coherent_row event F side 0 1 2 h10.symm h20 h21
    (fun i => by unfold event; split_ifs <;> simp) _ hsize
  intro hn
  refine ⟨⟨⟨0, by omega⟩, ?_⟩, ⟨⟨1, by omega⟩, ?_⟩⟩ <;> simp [event]

theorem selected_coherent (hp4 : 4 ≤ p) (h : ZMod m) :
    Incidence.Coherent (selected p hp h) :=
  pair_row_coherent p hp hm h.val _ false (by rw [card_fillers_add_pairs p hp]; omega)

theorem complement_coherent (hp4 : 4 ≤ p) (h : ZMod m) :
    Incidence.Coherent (fun w => aUsers p h.val \ selected p hp h w) := by
  let P := pairs p hp h.val
  let F := fillers p hp h.val
  have hf := fillers_disjoint p hp h.val
  have hc : (aUsers p h.val \ (P.support ∪ F)).card + P.count = p - p / 2 := by
    rw [Finset.card_sdiff_of_subset
      (Finset.union_subset P.support_subset (fillers_subset p hp h.val)),
      Finset.card_union_of_disjoint hf.symm, LocalPairs.card_support, card_aUsers p hp]
    have hs := card_fillers_add_pairs p hp h.val
    change F.card + P.count = p / 2 at hs
    dsimp [P, F] at hs ⊢
    omega
  have he (w : ZMod m) : aUsers p h.val \ selected p hp h w =
      P.row event (aUsers p h.val \ (P.support ∪ F)) true w :=
    P.complement_row event F hf false w
  simp only [he]
  exact pair_row_coherent p hp hm h.val _ true (by rw [hc]; omega)

end TorusEven.Entry.Shell
