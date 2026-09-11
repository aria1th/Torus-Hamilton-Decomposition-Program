-- STATUS: main-path
import TorusEven.Collar.MatchedPattern

namespace TorusEven.Collar.Incidence.MatchedData

variable {B Q Ω : Type*} [DecidableEq Ω] {A : B → Finset Ω} {m : ℕ}
variable (D : MatchedData (Q := Q) A m)

structure ResidualRows where
  pairs : ∀ b, LocalPairs (D.residual b)
  fillers : B → Finset Ω
  filler_subset : ∀ b, fillers b ⊆ D.residual b
  filler_disjoint : ∀ b, Disjoint (fillers b) (pairs b).support
  filler_card : ∀ b, (fillers b).card + (pairs b).count = D.quota b

noncomputable def rowsOfPairs (P : ∀ b, LocalPairs (D.residual b)) : D.ResidualRows := by
  choose F hF hd hc using fun b => (P b).exists_fillers_of_quota (D.quota b)
    (D.quota_bounds b (P b)).1 (D.quota_bounds b (P b)).2
  exact ⟨P, F, hF, hd, hc⟩

@[simp] theorem rowsOfPairs_pairs (P : ∀ b, LocalPairs (D.residual b)) :
    (D.rowsOfPairs P).pairs = P := rfl

namespace ResidualRows

variable {D} (R : D.ResidualRows) (hm : 4 ≤ m)

noncomputable def event (b : B) (i : Fin (R.pairs b).count) : ZMod m :=
  match D.query b with
  | none => fourRanks hm 0 (if i.val = 1 then 1 else 0)
  | some q => fourRanks hm (D.event q) (if i.val = 1 then 2 else 1)

noncomputable def row (b : B) (t : ZMod m) : Finset Ω :=
  (R.pairs b).row (R.event hm b) (R.fillers b) false t

theorem row_subset (b : B) (t : ZMod m) : R.row hm b t ⊆ D.residual b :=
  (R.pairs b).row_subset _ _ (R.filler_subset b) _ _

theorem row_card (b : B) (t : ZMod m) : (R.row hm b t).card = D.quota b :=
  ((R.pairs b).card_row _ _ (R.filler_disjoint b) _ _).trans (R.filler_card b)

theorem row_baseline {b : B} {q : Q} (h : D.query b = some q) :
    R.row hm b (D.event q) = R.row hm b (fourRanks hm (D.event q) 3) := by
  have hz (i : Fin (R.pairs b).count) : D.event q ≠ R.event hm b i := by
    simp only [event, h]
    split_ifs
    · simpa only [fourRanks_zero] using (fourRanks hm (D.event q)).injective.ne
        (by decide : (0 : Fin 4) ≠ 2)
    · simpa only [fourRanks_zero] using (fourRanks hm (D.event q)).injective.ne
        (by decide : (0 : Fin 4) ≠ 1)
  have hb (i : Fin (R.pairs b).count) : fourRanks hm (D.event q) 3 ≠ R.event hm b i := by
    simp only [event, h]
    split_ifs
    · exact (fourRanks hm (D.event q)).injective.ne (by decide : (3 : Fin 4) ≠ 2)
    · exact (fourRanks hm (D.event q)).injective.ne (by decide : (3 : Fin 4) ≠ 1)
  unfold row LocalPairs.row LocalPairs.chosen
  congr 2
  apply Function.Embedding.ext
  intro i
  simp only [LocalPairs.choice, hz, hb, if_false]

end ResidualRows
end TorusEven.Collar.Incidence.MatchedData
