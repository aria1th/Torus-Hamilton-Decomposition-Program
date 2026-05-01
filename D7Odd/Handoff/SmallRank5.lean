import D7Odd.Handoff.SmallIndex
import D7Odd.Handoff.SmallCertificates

namespace D7Odd
namespace Handoff

def smallReturnSix5 (c : Fin 7) (x : Fin 6 → ZMod 5) : Fin 6 → ZMod 5 :=
  sixOfRoot (smallReturn5 c (rootOfSix x))

structure SmallRank5Cert (c : Fin 7) where
  cert : RankArrayCert 15625
  ok : cert.ok = true
  comm : ∀ i : Fin 15625,
    indexToSix5 (cert.nextFunOfOk ok i) = smallReturnSix5 c (indexToSix5 i)

theorem smallReturnSix5_single_cycle_of_cert {c : Fin 7} (K : SmallRank5Cert c) :
    IsSingleCycleMap (smallReturnSix5 c) := by
  exact single_cycle_of_bijective_semiconj
    (f := K.cert.nextFunOfOk K.ok)
    (g := smallReturnSix5 c)
    (φ := indexToSix5)
    indexToSix5_bijective
    K.comm
    (RankArrayCert.singleCycle_of_ok K.cert K.ok)

theorem smallReturn5_single_cycle_of_cert {c : Fin 7} (K : SmallRank5Cert c) :
    IsSingleCycleMap (smallReturn5 c) := by
  exact single_cycle_of_bijective_semiconj
    (f := smallReturnSix5 c)
    (g := smallReturn5 c)
    (φ := rootOfSix)
    (Equiv.bijective (rootSixEquiv 5))
    (by intro x; unfold smallReturnSix5; rw [rootOfSix_sixOfRoot])
    (smallReturnSix5_single_cycle_of_cert K)

def SmallReturn5CycleTarget : Prop :=
  ∀ c : Fin 7, IsSingleCycleMap (smallReturn5 c)

def SmallRank5CertificateTarget : Prop :=
  ∀ c : Fin 7, Nonempty (SmallRank5Cert c)

theorem smallReturn5CycleTarget_of_rankCerts
    (h : SmallRank5CertificateTarget) :
    SmallReturn5CycleTarget := by
  intro c
  rcases h c with ⟨K⟩
  exact smallReturn5_single_cycle_of_cert K

end Handoff
end D7Odd
