import D7Odd.Handoff.SmallIndex
import D7Odd.Handoff.SmallCertificates

namespace D7Odd
namespace Handoff

def smallLayer5SelectorSix (c : Fin 7) (x : Fin 6 → ZMod 5) : Fin 6 → ZMod 5 :=
  sixOfRoot (smallLayer5 1 c (rootOfSix x))

structure SmallLayer5SelectorCert (c : Fin 7) where
  cert : FinMapArrayCert 15625
  ok : cert.ok = true
  comm : ∀ i : Fin 15625,
    indexToSix5 (cert.mapFunOfOk ok i) = smallLayer5SelectorSix c (indexToSix5 i)

theorem smallLayer5SelectorSix_bijective_of_cert {c : Fin 7}
    (K : SmallLayer5SelectorCert c) :
    Function.Bijective (smallLayer5SelectorSix c) := by
  exact bijective_of_bijective_semiconj
    (f := K.cert.mapFunOfOk K.ok)
    (g := smallLayer5SelectorSix c)
    (φ := indexToSix5)
    indexToSix5_bijective
    K.comm
    (FinMapArrayCert.bijective_of_ok K.cert K.ok)

theorem smallLayer5_selector_bijective_of_cert {c : Fin 7}
    (K : SmallLayer5SelectorCert c) :
    Function.Bijective (smallLayer5 1 c) := by
  exact bijective_of_bijective_semiconj
    (f := smallLayer5SelectorSix c)
    (g := smallLayer5 1 c)
    (φ := rootOfSix)
    (Equiv.bijective (rootSixEquiv 5))
    (by intro x; unfold smallLayer5SelectorSix; rw [rootOfSix_sixOfRoot])
    (smallLayer5SelectorSix_bijective_of_cert K)

end Handoff
end D7Odd
