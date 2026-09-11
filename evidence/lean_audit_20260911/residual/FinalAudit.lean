import TorusEven
import TorusAll

#print axioms TorusEven.Collar.RelativeCollarState.hamilton_decomposition_palette
#print axioms TorusEven.even_modulus_tori_all_dimensions_collar
#print axioms TorusEven.even_modulus_tori_all_dimensions
#print axioms TorusEven.Collar.hamilton_decomposition_of_entry_palette
#print axioms TorusAll.all_moduli_tori_all_dimensions
#print axioms TorusEven.Collar.MultitorusFactorization.repalette
#print axioms TorusEven.Collar.MultitorusFactorization.toCayleyOfPalette
#print axioms TorusEven.Collar.Incidence.IsPinnedSelection.map
#print axioms TorusEven.Collar.Incidence.evenOnComponents_of_pairs
#print axioms TorusEven.even_odd_degree
#print axioms TorusEven.d7_even
#print axioms TorusEven.even_successor
#print axioms TorusEven.Entry.Seed.hamilton_decomposition
#print axioms TorusEven.Entry.Seed.coreIndex
#print axioms TorusEven.Entry.Seed.activeAt
#print axioms TorusEven.Entry.Seed.corePresent_iff_activeAt
#print axioms TorusEven.Entry.Seed.anchorBlockNat
#print axioms TorusEven.Entry.Seed.anchorRowNat
#print axioms TorusEven.Entry.Seed.blockRanks
#print axioms TorusEven.Entry.Seed.anchorBlock
#print axioms TorusEven.Entry.Seed.anchorRow
#print axioms TorusEven.Entry.Seed.blockRanks_apply
#print axioms TorusEven.Entry.Seed.anchor_coordinates
#print axioms TorusEven.Entry.Seed.activeAt_anchor
#print axioms TorusEven.Entry.Seed.mateIndex
#print axioms TorusEven.Entry.Seed.mate
#print axioms TorusEven.Entry.Seed.auxiliaryNat
#print axioms TorusEven.Entry.Seed.mem_auxiliaryNat
#print axioms TorusEven.Entry.Seed.mate_eligible_nat
#print axioms TorusEven.Entry.Seed.auxiliary
#print axioms TorusEven.Entry.Seed.auxiliary_at_ranks
#print axioms TorusEven.Entry.Seed.matched
#print axioms TorusEven.Entry.Seed.matched_fullSupport
#print axioms TorusEven.Entry.Seed.nonmateIndex
#print axioms TorusEven.Entry.Seed.nonmateOrder
#print axioms TorusEven.Entry.Seed.nonmateOrder_mem
#print axioms TorusEven.Entry.Seed.nonmateOrder_surjective
#print axioms TorusEven.Entry.Seed.nonmateEquiv
#print axioms TorusEven.Entry.Seed.nonmatePairs
#print axioms TorusEven.Entry.Seed.nonmatePairs_val
#print axioms TorusEven.Entry.Seed.nonmates
#print axioms TorusEven.Entry.Seed.residualNat
#print axioms TorusEven.Entry.Seed.mem_nonmates_iff
#print axioms TorusEven.Entry.Seed.matched_nonmates
#print axioms TorusEven.Entry.Seed.residualNat_subset
#print axioms TorusEven.Entry.Seed.residualComponent
#print axioms TorusEven.Entry.Seed.residual_same_nat
#print axioms TorusEven.Entry.Seed.residual_same_witness
#print axioms TorusEven.Entry.Seed.residual_even_A
#print axioms TorusEven.Entry.Seed.residual_even_B
#print axioms TorusEven.Entry.Seed.residual_odd_A
#print axioms TorusEven.Entry.Seed.residual_odd_B
#print axioms TorusEven.Entry.Seed.residual_odd_connected
#print axioms TorusEven.Entry.Seed.residual_pair_same
#print axioms TorusEven.Entry.Seed.residual_even
#print axioms TorusEven.Entry.Seed.exists_matchedSelection
#print axioms TorusEven.Entry.Seed.residualWitness
#print axioms TorusEven.Entry.Seed.mem_residualNat_of_witness
#print axioms TorusEven.Entry.Seed.labels_symm_left_fst
#print axioms TorusEven.Entry.Seed.labels_symm_right_fst
#print axioms TorusEven.Entry.Seed.exists_blockSelection
#print axioms TorusEven.Collar.SplitResolution
#print axioms TorusEven.Collar.RelativeCollarState.resolution
#print axioms TorusEven.Collar.RelativeCollarState.hamilton_decomposition
#print axioms TorusEven.Collar.hamilton_decomposition_of_entry
#print axioms TorusEven.even_degree_collar
#print axioms TorusEven.even_modulus_tori_all_dimensions_of_collar
#print axioms RoundComposite.Concrete.odd_modulus_tori_all_dimensions_v75

example : TorusEven.EvenOddDegreeGoal := TorusEven.even_odd_degree
example : TorusEven.EvenModulusToriAllDimensionsGoal := TorusEven.even_modulus_tori_all_dimensions
example : TorusEven.EvenModulusToriAllDimensionsGoal := TorusEven.even_modulus_tori_all_dimensions_collar
example : ∀ {d m : ℕ}, 2 ≤ d → 3 ≤ m → Shared.CayleyHamiltonDecomposition d m :=
  TorusAll.all_moduli_tori_all_dimensions
