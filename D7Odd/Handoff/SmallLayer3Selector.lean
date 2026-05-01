import D7Odd.Handoff.SmallIndex
import D7Odd.Handoff.SmallCertificates

namespace D7Odd
namespace Handoff

def smallLayer3SelectorSix (c : Fin 7) (x : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 :=
  sixOfRoot (smallLayer3 1 c (rootOfSix x))

structure SmallLayer3SelectorCert (c : Fin 7) where
  cert : FinMapArrayCert 729
  ok : cert.ok = true
  comm : ∀ i : Fin 729,
    indexToSix3 (cert.mapFunOfOk ok i) = smallLayer3SelectorSix c (indexToSix3 i)

theorem smallLayer3SelectorSix_bijective_of_cert {c : Fin 7}
    (K : SmallLayer3SelectorCert c) :
    Function.Bijective (smallLayer3SelectorSix c) := by
  exact bijective_of_bijective_semiconj
    (f := K.cert.mapFunOfOk K.ok)
    (g := smallLayer3SelectorSix c)
    (φ := indexToSix3)
    indexToSix3_bijective
    K.comm
    (FinMapArrayCert.bijective_of_ok K.cert K.ok)

theorem smallLayer3_selector_bijective_of_cert {c : Fin 7}
    (K : SmallLayer3SelectorCert c) :
    Function.Bijective (smallLayer3 1 c) := by
  exact bijective_of_bijective_semiconj
    (f := smallLayer3SelectorSix c)
    (g := smallLayer3 1 c)
    (φ := rootOfSix)
    (Equiv.bijective (rootSixEquiv 3))
    (by intro x; unfold smallLayer3SelectorSix; rw [rootOfSix_sixOfRoot])
    (smallLayer3SelectorSix_bijective_of_cert K)

end Handoff
end D7Odd
