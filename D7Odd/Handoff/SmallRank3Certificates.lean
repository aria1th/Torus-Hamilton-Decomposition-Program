import D7Odd.Handoff.SmallRank3
import D7Odd.Handoff.SmallLayer3SelectorData0
import D7Odd.Handoff.SmallLayer3SelectorData1
import D7Odd.Handoff.SmallLayer3SelectorData2
import D7Odd.Handoff.SmallLayer3SelectorData3
import D7Odd.Handoff.SmallLayer3SelectorData4
import D7Odd.Handoff.SmallLayer3SelectorData5
import D7Odd.Handoff.SmallLayer3SelectorData6

namespace D7Odd
namespace Handoff

theorem smallLayer3_t0_bijective : ∀ c, Function.Bijective (smallLayer3 0 c) := by
  intro c
  unfold smallLayer3 smallDir3 offset3
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_ne_one, ↓reduceIte]
  exact addQRoot_bijective (addMod7 c 2)

theorem smallLayer3_t2_bijective : ∀ c, Function.Bijective (smallLayer3 2 c) := by
  intro c
  unfold smallLayer3 smallDir3 offset3
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, OfNat.ofNat_ne_one, ↓reduceIte]
  exact addQRoot_bijective (addMod7 c 4)

theorem smallLayer3_nonSelector_bijective :
    ∀ t c, t ≠ (1 : Fin 3) → Function.Bijective (smallLayer3 t c) := by
  intro t c ht
  fin_cases t
  · exact smallLayer3_t0_bijective c
  · contradiction
  · exact smallLayer3_t2_bijective c

set_option maxHeartbeats 10000000 in
-- Native checker tests row Latin after transporting root states to six coordinates.
set_option linter.style.nativeDecide false in
theorem smallDir3_latin_six :
    ∀ t x, Function.Bijective fun c : Fin 7 => smallDir3 t (rootOfSix x) c := by
  native_decide

theorem smallDir3_latin :
    ∀ t w, Function.Bijective fun c : Fin 7 => smallDir3 t w c := by
  intro t w
  simpa [rootOfSix_sixOfRoot] using smallDir3_latin_six t (sixOfRoot w)

def SmallLayer3SelectorBijectiveTarget : Prop :=
  ∀ c, Function.Bijective (smallLayer3 1 c)

theorem smallLayer3_selector_bijective : SmallLayer3SelectorBijectiveTarget := by
  intro c
  fin_cases c
  · exact smallLayer3_selector_bijective_of_cert smallLayer3SelectorCertColor0
  · exact smallLayer3_selector_bijective_of_cert smallLayer3SelectorCertColor1
  · exact smallLayer3_selector_bijective_of_cert smallLayer3SelectorCertColor2
  · exact smallLayer3_selector_bijective_of_cert smallLayer3SelectorCertColor3
  · exact smallLayer3_selector_bijective_of_cert smallLayer3SelectorCertColor4
  · exact smallLayer3_selector_bijective_of_cert smallLayer3SelectorCertColor5
  · exact smallLayer3_selector_bijective_of_cert smallLayer3SelectorCertColor6

theorem smallLayer3_bijective :
    ∀ t c, Function.Bijective (smallLayer3 t c) := by
  intro t c
  by_cases ht : t = (1 : Fin 3)
  · subst t
    exact smallLayer3_selector_bijective c
  · exact smallLayer3_nonSelector_bijective t c ht

theorem smallCertificateTarget3 : SmallCertificateTarget3 :=
  ⟨smallLayer3_bijective, smallDir3_latin, smallReturn3_single_cycle⟩

theorem smallLayer3BijectiveTarget : SmallLayer3BijectiveTarget :=
  smallLayer3_bijective

theorem smallDir3LatinTarget : SmallDir3LatinTarget :=
  smallDir3_latin

theorem smallLayer3SelectorBijectiveTarget : SmallLayer3SelectorBijectiveTarget :=
  smallLayer3_selector_bijective

theorem smallCertificateTarget3WithRank : SmallCertificateTarget3WithRank :=
  ⟨smallLayer3_bijective, smallDir3_latin, smallReturn3_single_cycle⟩

end Handoff
end D7Odd
