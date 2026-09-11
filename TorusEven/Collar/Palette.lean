-- STATUS: main-path
import TorusEven.Collar.Multitorus

namespace TorusEven.Collar

variable {C D I : Type*} [Fintype C] [Fintype D] [DecidableEq I] {m : ℕ}

def MultitorusFactorization.repalette (F : MultitorusFactorization C I m) (e : D ≃ C) :
    MultitorusFactorization D I m where
  width := F.width
  width_pos := F.width_pos
  direction c := F.direction (e c)
  step c := F.step (e c)
  step_eq c := F.step_eq (e c)
  quota x i := by
    have hc := Fintype.card_congr (Equiv.subtypeEquiv e (fun c => Iff.rfl) :
      {c : D // F.direction (e c) x = i} ≃ {c : C // F.direction c x = i})
    have he : (Finset.univ.filter (fun c : D => F.direction (e c) x = i)).card =
        (Finset.univ.filter (fun c : C => F.direction c x = i)).card := by
      simpa only [Fintype.card_subtype] using hc
    exact he.trans (F.quota x i)

noncomputable def MultitorusFactorization.toCayleyOfPalette [Fintype I]
    (F : MultitorusFactorization C I m) (hw : ∀ i, F.width i = 1)
    (hH : ∀ c, Shared.IsSingleCycleMap (F.step c)) :
    Shared.CayleyDecomposition (Fintype.card C) m :=
  (F.repalette (Fintype.equivFin C).symm).toCayleyOfUnitWidths hw
    (fun c => hH ((Fintype.equivFin C).symm c))

end TorusEven.Collar
