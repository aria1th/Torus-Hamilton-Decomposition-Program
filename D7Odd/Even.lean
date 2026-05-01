import D7Odd.Cayley
import D7Odd.Handoff.PrimeCanonicalBridge

namespace D7Odd

namespace D7Even

def RootFlatTarget (m : Nat) [NeZero m] : Prop :=
  ∃ S : Handoff.RootFlatSchedule m,
    S.rowLatin ∧ S.layerBijective ∧ S.returnsSingleCycle

def CertificateTarget (m : Nat) [NeZero m] : Prop :=
  Even m ∧ RootFlatTarget m

abbrev primeD7 :=
  Handoff.PrimeRoot.PrimeDimension.seven

def PrimeRootFlatTarget (m : Nat) [NeZero m] : Prop :=
  ∃ S : primeD7.RootFlatSchedule m,
    S.rowLatin ∧ S.layerBijective ∧ S.returnsSingleCycle

def PrimeCertificateTarget (m : Nat) [NeZero m] : Prop :=
  Even m ∧ PrimeRootFlatTarget m

theorem root_flat_target_of_prime_root_flat_target {m : Nat} [NeZero m]
    (h : PrimeRootFlatTarget m) :
    RootFlatTarget m := by
  rcases h with ⟨S, hRow, hLayer, hReturn⟩
  exact ⟨Handoff.PrimeRoot.PrimeDimension.rootFlatScheduleFixedOfSeven S,
    hRow, hLayer, hReturn⟩

theorem certificate_target_of_prime_certificate_target {m : Nat} [NeZero m]
    (h : PrimeCertificateTarget m) :
    CertificateTarget m := by
  exact ⟨h.1, root_flat_target_of_prime_root_flat_target h.2⟩

theorem handoff_from_root_flat_target {m : Nat} [NeZero m]
    (h : RootFlatTarget m) :
    Handoff.HamiltonDecompositionD7 m := by
  rcases h with ⟨S, hRow, hLayer, hReturn⟩
  exact Handoff.certificate_implies_hamilton
    { schedule := S
      rowLatin := hRow
      layerBijective := hLayer
      returnsSingleCycle := hReturn }

theorem shared_layered_from_root_flat_target {m : Nat} [NeZero m]
    (h : RootFlatTarget m) :
    Shared.RootFlatLayeredHamiltonDecomposition
      Handoff.Color Handoff.Direction (Handoff.RootState7 m) m :=
  Handoff.rootFlatLayeredHamilton_of_hamiltonDecompositionD7
    (handoff_from_root_flat_target h)

theorem torus_from_root_flat_target {m : Nat} [NeZero m]
    (h : RootFlatTarget m) :
    TorusHamiltonDecompositionD7 m := by
  exact torusHamiltonDecompositionD7_of_handoff
    (handoff_from_root_flat_target h)

theorem cayley_from_root_flat_target {m : Nat} [NeZero m]
    (h : RootFlatTarget m) :
    CayleyHamiltonDecompositionD7 m := by
  exact cayleyHamiltonDecomposition_of_torus
    (torus_from_root_flat_target h)

theorem D7_even_handoff_from_target {m : Nat} [NeZero m]
    (h : CertificateTarget m) :
    Handoff.HamiltonDecompositionD7 m := by
  exact handoff_from_root_flat_target h.2

theorem D7_even_shared_layered_from_target {m : Nat} [NeZero m]
    (h : CertificateTarget m) :
    Shared.RootFlatLayeredHamiltonDecomposition
      Handoff.Color Handoff.Direction (Handoff.RootState7 m) m :=
  shared_layered_from_root_flat_target h.2

theorem D7_even_torus_from_target {m : Nat} [NeZero m]
    (h : CertificateTarget m) :
    TorusHamiltonDecompositionD7 m := by
  exact torus_from_root_flat_target h.2

theorem D7_even_cayley_from_target {m : Nat} [NeZero m]
    (h : CertificateTarget m) :
    CayleyHamiltonDecompositionD7 m := by
  exact cayley_from_root_flat_target h.2

theorem handoff_from_prime_root_flat_target {m : Nat} [NeZero m]
    (h : PrimeRootFlatTarget m) :
    Handoff.HamiltonDecompositionD7 m := by
  exact handoff_from_root_flat_target
    (root_flat_target_of_prime_root_flat_target h)

theorem shared_layered_from_prime_root_flat_target {m : Nat} [NeZero m]
    (h : PrimeRootFlatTarget m) :
    Shared.RootFlatLayeredHamiltonDecomposition
      Handoff.Color Handoff.Direction (Handoff.RootState7 m) m :=
  shared_layered_from_root_flat_target
    (root_flat_target_of_prime_root_flat_target h)

theorem torus_from_prime_root_flat_target {m : Nat} [NeZero m]
    (h : PrimeRootFlatTarget m) :
    TorusHamiltonDecompositionD7 m := by
  exact torus_from_root_flat_target
    (root_flat_target_of_prime_root_flat_target h)

theorem cayley_from_prime_root_flat_target {m : Nat} [NeZero m]
    (h : PrimeRootFlatTarget m) :
    CayleyHamiltonDecompositionD7 m := by
  exact cayley_from_root_flat_target
    (root_flat_target_of_prime_root_flat_target h)

theorem D7_even_handoff_from_prime_target {m : Nat} [NeZero m]
    (h : PrimeCertificateTarget m) :
    Handoff.HamiltonDecompositionD7 m := by
  exact handoff_from_prime_root_flat_target h.2

theorem D7_even_shared_layered_from_prime_target {m : Nat} [NeZero m]
    (h : PrimeCertificateTarget m) :
    Shared.RootFlatLayeredHamiltonDecomposition
      Handoff.Color Handoff.Direction (Handoff.RootState7 m) m :=
  shared_layered_from_prime_root_flat_target h.2

theorem D7_even_torus_from_prime_target {m : Nat} [NeZero m]
    (h : PrimeCertificateTarget m) :
    TorusHamiltonDecompositionD7 m := by
  exact torus_from_prime_root_flat_target h.2

theorem D7_even_cayley_from_prime_target {m : Nat} [NeZero m]
    (h : PrimeCertificateTarget m) :
    CayleyHamiltonDecompositionD7 m := by
  exact cayley_from_prime_root_flat_target h.2

end D7Even

end D7Odd
