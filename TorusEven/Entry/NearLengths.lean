-- STATUS: main-path
import TorusEven.Entry.Defect

namespace TorusEven.Entry.NearCore

open Collar Surgery

variable {m : ℕ} [NeZero m] (heven : Even m)

def slide (t : ZMod m) : Equiv.Perm (Point m) :=
  chart.symm.trans ((Equiv.prodCongr
    (Equiv.prodCongr (Equiv.refl _) (Equiv.addRight t)) (Equiv.refl _)).trans chart)

omit [NeZero m] in
theorem slide_chart (t : ZMod m) (p : (ZMod m × ZMod m) × ZMod m) :
    slide t (chart p) = chart ((p.1.1, p.1.2 + t), p.2) := by
  rcases p with ⟨⟨h, w⟩, y⟩
  simp [slide]

omit [NeZero m] in
theorem defect_chart (p : (ZMod m × ZMod m) × ZMod m) :
    defect heven (chart p) = parityMap heven p.1.2 - (p.1.1.val - 2 : ℕ) := by
  simp only [defect, height_chart]
  rfl

omit [NeZero m] in
theorem defect_slide (t : ZMod m) (v : Point m) :
    defect heven (slide t v) = defect heven v + parityMap heven t := by
  obtain ⟨p, rfl⟩ := chart.surjective v
  rw [slide_chart, defect_chart, defect_chart, map_add]
  ring

theorem defect_fiber_card (z : ZMod 2) :
    Nat.card {v : Point m // defect heven v = z} = m ^ 3 / 2 := by
  classical
  have he (z : ZMod 2) : Nat.card {v : Point m // defect heven v = z} =
      Nat.card {v : Point m // defect heven v = 0} := by
    obtain ⟨t, ht⟩ := ZMod.castHom_surjective heven.two_dvd (-z)
    change parityMap heven t = -z at ht
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (slide t) (fun v => by
      rw [defect_slide, ht, ← sub_eq_add_neg, sub_eq_zero])
  have hs := Nat.card_congr (Equiv.sigmaFiberEquiv (defect heven))
  rw [Nat.card_sigma] at hs
  simp only [he, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul] at hs
  have hp : Nat.card (Point m) = m ^ 3 := by
    simp [Point, Nat.card_eq_fintype_card]
  rw [hp] at hs
  rw [he]
  omega

include heven in
theorem orbit_card_two (hm : 4 ≤ m) (v : Point m) :
    Nat.card (orbitSet (step 2) v) = m ^ 3 / 2 := by
  exact (Nat.card_congr (Equiv.subtypeEquivRight
    (fun u => orbit_defect_iff hm heven v u))).trans (defect_fiber_card heven _)

end TorusEven.Entry.NearCore
