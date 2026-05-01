import D7Odd.Handoff.SmallRank5Data0
import D7Odd.Handoff.SmallRank5Data1
import D7Odd.Handoff.SmallRank5Data2
import D7Odd.Handoff.SmallRank5Data3
import D7Odd.Handoff.SmallRank5Data4
import D7Odd.Handoff.SmallRank5Data5
import D7Odd.Handoff.SmallRank5Data6
import D7Odd.Handoff.SmallLayer5SelectorData0
import D7Odd.Handoff.SmallLayer5SelectorData1
import D7Odd.Handoff.SmallLayer5SelectorData2
import D7Odd.Handoff.SmallLayer5SelectorData3
import D7Odd.Handoff.SmallLayer5SelectorData4
import D7Odd.Handoff.SmallLayer5SelectorData5
import D7Odd.Handoff.SmallLayer5SelectorData6

namespace D7Odd
namespace Handoff

theorem smallLayer5_t0_bijective : ∀ c, Function.Bijective (smallLayer5 0 c) := by
  intro c
  unfold smallLayer5 smallDir5 offset5
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_ne_one, ↓reduceIte]
  exact addQRoot_bijective (addMod7 c 1)

theorem smallLayer5_t2_bijective : ∀ c, Function.Bijective (smallLayer5 2 c) := by
  intro c
  unfold smallLayer5 smallDir5 offset5
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, OfNat.ofNat_ne_one, ↓reduceIte]
  exact addQRoot_bijective (addMod7 c 2)

theorem smallLayer5_t3_bijective : ∀ c, Function.Bijective (smallLayer5 3 c) := by
  intro c
  unfold smallLayer5 smallDir5 offset5
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, OfNat.ofNat_ne_one, ↓reduceIte]
  exact addQRoot_bijective (addMod7 c 5)

theorem smallLayer5_t4_bijective : ∀ c, Function.Bijective (smallLayer5 4 c) := by
  intro c
  unfold smallLayer5 smallDir5 offset5
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ, OfNat.ofNat_ne_one, ↓reduceIte]
  exact addQRoot_bijective (addMod7 c 6)

theorem smallLayer5_nonSelector_bijective :
    ∀ t c, t ≠ (1 : Fin 5) → Function.Bijective (smallLayer5 t c) := by
  intro t c ht
  fin_cases t
  · exact smallLayer5_t0_bijective c
  · contradiction
  · exact smallLayer5_t2_bijective c
  · exact smallLayer5_t3_bijective c
  · exact smallLayer5_t4_bijective c

set_option maxHeartbeats 50000000 in
-- Native checker tests row Latin after transporting root states to six coordinates.
set_option linter.style.nativeDecide false in
theorem smallDir5_latin_six :
    ∀ t x, Function.Bijective fun c : Fin 7 => smallDir5 t (rootOfSix x) c := by
  native_decide

theorem smallDir5_latin :
    ∀ t w, Function.Bijective fun c : Fin 7 => smallDir5 t w c := by
  intro t w
  simpa [rootOfSix_sixOfRoot] using smallDir5_latin_six t (sixOfRoot w)

def SmallLayer5SelectorBijectiveTarget : Prop :=
  ∀ c, Function.Bijective (smallLayer5 1 c)

theorem smallLayer5_selector_bijective : SmallLayer5SelectorBijectiveTarget := by
  intro c
  fin_cases c
  · exact smallLayer5_selector_bijective_of_cert smallLayer5SelectorCertColor0
  · exact smallLayer5_selector_bijective_of_cert smallLayer5SelectorCertColor1
  · exact smallLayer5_selector_bijective_of_cert smallLayer5SelectorCertColor2
  · exact smallLayer5_selector_bijective_of_cert smallLayer5SelectorCertColor3
  · exact smallLayer5_selector_bijective_of_cert smallLayer5SelectorCertColor4
  · exact smallLayer5_selector_bijective_of_cert smallLayer5SelectorCertColor5
  · exact smallLayer5_selector_bijective_of_cert smallLayer5SelectorCertColor6

theorem smallLayer5_bijective :
    ∀ t c, Function.Bijective (smallLayer5 t c) := by
  intro t c
  by_cases ht : t = (1 : Fin 5)
  · subst t
    exact smallLayer5_selector_bijective c
  · exact smallLayer5_nonSelector_bijective t c ht

theorem smallRank5CertificateTarget : SmallRank5CertificateTarget := by
  intro c
  fin_cases c
  · exact ⟨smallRank5CertColor0⟩
  · exact ⟨smallRank5CertColor1⟩
  · exact ⟨smallRank5CertColor2⟩
  · exact ⟨smallRank5CertColor3⟩
  · exact ⟨smallRank5CertColor4⟩
  · exact ⟨smallRank5CertColor5⟩
  · exact ⟨smallRank5CertColor6⟩

theorem smallReturn5CycleTarget : SmallReturn5CycleTarget :=
  smallReturn5CycleTarget_of_rankCerts smallRank5CertificateTarget

theorem smallCertificateTarget5 : SmallCertificateTarget5 :=
  ⟨smallLayer5_bijective, smallDir5_latin, smallReturn5CycleTarget⟩

theorem smallLayer5SelectorBijectiveTarget : SmallLayer5SelectorBijectiveTarget :=
  smallLayer5_selector_bijective

end Handoff
end D7Odd
