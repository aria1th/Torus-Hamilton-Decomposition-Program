-- STATUS: main-path
import TorusEven.Entry.Star.Geometry
import TorusEven.Entry.LayerSums

namespace TorusEven.Entry.Star

open Collar

variable {m : ℕ} [NeZero m] (hm : 4 ≤ m)

def cornerPlus : Plane m := (1, -1)
def cornerMinus : Plane m := (-1, 1)

def word (q : ZMod m × ZMod 2) : Plane m :=
  if q.2 = 0 then (if q.1 = 0 then cornerPlus else (q.1, 0))
  else if q.1 = 0 then cornerMinus else (0, q.1)

def wordStep : Equiv.Perm (ZMod m × ZMod 2) :=
  lift (Equiv.addRight 1) (fun t => if t = -1 then 1 else 0)

theorem wordStep_singleCycle : Shared.IsSingleCycleMap (wordStep (m := m)) := by
  apply lift_singleCycle _ height_singleCycle _ 0
  simp

include hm

omit [NeZero m] in
theorem word_injective : Function.Injective (word (m := m)) := by
  have h1 := one_ne_zero_of_four_le hm
  have hn := one_ne_neg_one hm
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rintro ⟨s, z⟩ ⟨t, z'⟩ h
  rcases hz z with rfl | rfl <;> rcases hz z' with rfl | rfl <;>
    by_cases hs : s = 0 <;> by_cases ht : t = 0 <;>
    simp_all [word, cornerPlus, cornerMinus, Prod.mk.injEq]

omit [NeZero m] in
theorem surgery_zero_corners : surgeryMap 0 (cornerPlus (m := m)) = (1, 0) ∧
    surgeryMap 0 (cornerMinus (m := m)) = (0, 1) := by
  have h1 := one_ne_zero_of_four_le hm
  have hn := one_ne_neg_one hm
  constructor <;>
    simp [surgeryMap, cornerPlus, cornerMinus, starRow, starRayRow, generator, rotate,
      h1, Ne.symm hn]

omit [NeZero m] hm in
theorem surgery_zero_x (s : ZMod m) (hs : s ≠ 0) :
    surgeryMap 0 (s, 0) = if s = -1 then cornerMinus else (s + 1, 0) := by
  have hrow : starRow s (0 : ZMod m) = starRayRow 2 (-s) := by simp [starRow, hs]
  simp only [surgeryMap, hrow]
  by_cases hn : s = -1
  · subst s
    simp [starRayRow, generator, rotate, cornerMinus]
  · have hn' : -s ≠ 1 := by intro h; apply hn; linear_combination -h
    simp only [starRayRow, if_neg hn']
    by_cases hs1 : -s = -1
    · simp [hs1, generator, rotate, hn]
    · simp [hs1, generator, reflection, hn]

omit [NeZero m] in
theorem surgery_zero_y (s : ZMod m) (hs : s ≠ 0) :
    surgeryMap 0 (0, s) = if s = -1 then cornerPlus else (0, s + 1) := by
  have hn1 := one_ne_neg_one hm
  have hrow : starRow (0 : ZMod m) s = starRayRow 1 s := by simp [starRow, hs]
  simp only [surgeryMap, hrow]
  by_cases hn : s = -1
  · subst s
    simp [starRayRow, Ne.symm hn1, generator, rotate, cornerPlus]
  · simp only [starRayRow]
    by_cases hs1 : s = 1
    · simp [hs1, generator, rotate, hn1]
    · simp [hs1, hn, generator, reflection]

omit [NeZero m] in
theorem surgery_word (q : ZMod m × ZMod 2) : surgeryMap 0 (word q) = word (wordStep q) := by
  have h1 := one_ne_zero_of_four_le hm
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases q with ⟨s, z⟩
  rcases hz z with rfl | rfl
  all_goals
    by_cases hs : s = 0
    · subst s
      simp [word, wordStep, lift, h1, surgery_zero_corners hm]
    · by_cases hn : s = -1
      · subst s
        simp [word, wordStep, lift, h1, surgery_zero_x _ hs, surgery_zero_y hm _ hs,
          show (1 : ZMod 2) + 1 = 0 by decide]
      · have hp : s + 1 ≠ 0 := by intro h; apply hn; linear_combination h
        simp [word, wordStep, lift, hs, hn, hp, surgery_zero_x _ hs, surgery_zero_y hm _ hs]

omit [NeZero m] hm in
theorem surgery_zero_outside (p : Plane m) (hp : p ∉ Set.range (word (m := m))) :
    surgeryMap 0 p = p := by
  rcases plane_cases p with rfl | ⟨z, t, ht, rfl⟩ | ⟨ha, hb, hab⟩
  · simp [surgeryMap, starRow, generator]
  · fin_cases z
    · by_cases h1 : t = 1
      · exact False.elim (hp ⟨(0, 0), by simp [word, ray, cornerPlus, h1]⟩)
      · by_cases hn : t = -1
        · exact False.elim (hp ⟨(0, 1), by simp [word, ray, cornerMinus, hn]⟩)
        · simp only [surgeryMap, row_ray _ ht, starRayRow, if_neg h1, if_neg hn]
          simp [reflection, generator, Equiv.swap_apply_def]
    · exact False.elim (hp ⟨(t, 1), by simp [word, ray, ht]⟩)
    · exact False.elim (hp ⟨(-t, 0), by simp [word, ray, ht]⟩)
  · simp [surgeryMap, starRow, ha, hb, hab, generator]

noncomputable def zeroPerm : Equiv.Perm (Plane m) :=
  wordStep.viaEmbedding ⟨word, word_injective hm⟩

theorem zeroPerm_apply (p : Plane m) : zeroPerm hm p = surgeryMap 0 p := by
  classical
  by_cases hp : p ∈ Set.range (word (m := m))
  · obtain ⟨q, rfl⟩ := hp
    exact (wordStep.viaEmbedding_apply ⟨word, word_injective hm⟩ q).trans
      (surgery_word hm q).symm
  · exact (wordStep.viaEmbedding_apply_of_notMem ⟨word, word_injective hm⟩ p hp).trans
      (surgery_zero_outside p hp).symm

end TorusEven.Entry.Star
