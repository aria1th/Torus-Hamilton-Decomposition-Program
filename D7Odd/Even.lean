import D7Odd.Cayley

namespace D7Odd

namespace D7Even

def RootFlatTarget (m : Nat) [NeZero m] : Prop :=
  ∃ S : Handoff.RootFlatSchedule m,
    S.rowLatin ∧ S.layerBijective ∧ S.returnsSingleCycle

def CertificateTarget (m : Nat) [NeZero m] : Prop :=
  Even m ∧ RootFlatTarget m

theorem handoff_from_root_flat_target {m : Nat} [NeZero m]
    (h : RootFlatTarget m) :
    Handoff.HamiltonDecompositionD7 m := by
  rcases h with ⟨S, hRow, hLayer, hReturn⟩
  exact Handoff.certificate_implies_hamilton
    { schedule := S
      rowLatin := hRow
      layerBijective := hLayer
      returnsSingleCycle := hReturn }

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

theorem D7_even_torus_from_target {m : Nat} [NeZero m]
    (h : CertificateTarget m) :
    TorusHamiltonDecompositionD7 m := by
  exact torus_from_root_flat_target h.2

theorem D7_even_cayley_from_target {m : Nat} [NeZero m]
    (h : CertificateTarget m) :
    CayleyHamiltonDecompositionD7 m := by
  exact cayley_from_root_flat_target h.2

end D7Even

end D7Odd
