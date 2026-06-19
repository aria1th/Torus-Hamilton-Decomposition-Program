# Odd multitori split formalization - 2026-06-18

This records the urgent odd-modulus proof route:

```text
T_m(d)
  -> split parallel classes a into ceil(a/2), floor(a/2)
  -> T_m(1,...,1) = D_d(m)
```

Lean file:

- `Shared/OddMultitoriSplit.lean`

## Lean Status

Completion check - 2026-06-19:

- `lake env lean Shared/OddMultitoriSplit.lean` passes with no diagnostics.
- `lake env lean Shared.lean` passes.
- `lake build Shared` completes successfully.  The build still reports existing
  style/linter warnings in other modules, plus flexible-tactic style warnings
  in this fast-route file, but no proof obligation fails.
- The closed theorem for the fast route is
  `OddMultitori.oddDirectedTorusGoal_replicated_shortcut_closed :
  OddMultitori.OddDirectedTorusGoal`.
- The original broad `SplittingLemmaGoal` and `BalancingLemmaGoal` are still
  preserved as named comparison/placeholder targets; the completed proof route
  uses the replicated block shortcut and no longer depends on them.
- The manuscript source `directed_tori_cyclic_splitting.tex` now contains an
  appendix explaining the paper-to-Lean correspondence.  That TeX file lives
  outside this Lean git repository, so it is included in the release artifact
  rather than in this repository commit.

Closed in Lean:

- multitorus vertex/parallel-arc model `OddMultitori.Vertex` and
  `OddMultitori.Arc`;
- multitorus Hamilton decomposition record
  `OddMultitori.Decomposition`;
- one-part base decomposition `T_m(d)`;
- list-context completion lemma
  `OddMultitori.splitPartToOnesInContext`;
- theorem
  `OddMultitori.allOnes_hasDecomposition_of_splitting`, proving that the
  splitting lemma iterated from `[d]` reaches `List.replicate d 1`.
- `OddMultitori.standardBridgeGoal`: the all-ones multitorus
  `T_m(1,...,1)` is converted to the repository's standard
  `Shared.CayleyHamiltonDecomposition d m` interface.
- `OddMultitori.oddDirectedTorusGoal_of_splitting_closedBridge`: a corrected
  splitting lemma alone implies the final odd directed torus target.
- `OddMultitori.MFiberedDecomposition`: an explicit `m`-fibered strengthening
  of a multitorus decomposition, with vertices partitioned as
  `Block × Fin m` and direction-colour sets constant along each fiber.
- `OddMultitori.onePart_hasMFiberedDecomposition`: the base decomposition
  of `T_m(d)` is closed as `m`-fibered.
- `OddMultitori.allOnes_hasMFiberedDecomposition_of_mFibered_splitting` and
  `OddMultitori.oddDirectedTorusGoal_of_mFibered_splitting_closedBridge`:
  a fibered splitting lemma alone implies the final odd directed torus target.
- `OddMultitori.oddDirectedTorusGoal_of_replicated_balancing`: the final target
  follows from the replicated balancing shortcut once its balancing-to-lift
  bridge is supplied.

Refuted in Lean:

- The balancing lemma from the prompt is false as stated.  The counterexample
  is `m=3`, `a=2`, `X=Fin 3`, one right vertex, and two parallel incidences
  from each `x` to that right vertex.  The hypotheses hold, but selecting one
  incidence at each left vertex forces the only selected right degree to be
  `3`, not a unit modulo `3`.
- Lean names:
  `OddMultitori.counterBalancing_hypotheses` and
  `OddMultitori.counterBalancing_no_unitSelection`.
- This counterexample uses parallel incidences at a left vertex.  It refutes
  the incidence-multigraph reading currently formalized in Lean.  If the paper
  intends an ordinary simple bipartite graph, that restriction must be stated
  explicitly; under that narrower reading the present Lean counterexample
  becomes a warning sign and the missing Hamilton-incidence proof obligation
  below remains.

## Verdict on the Balancing Lemma

The balancing lemma should be treated as refuted in its stated generality, not
as a lemma with a missing routine detail.  The obstruction is component-level:
alternating-trail switches cannot move selected incidences between connected
components.  For a component `C`, the total selected count is fixed as

```text
S_C = floor(a/2) * |X_C|.
```

Therefore any corrected statement must at least require unit residues
`u_y mod m` for the right vertices `y in Y_C` such that

```text
sum_{y in Y_C} u_y = S_C mod m.
```

The one-right-vertex counterexample fails exactly this condition: `S_C = 3`
is `0 mod 3`, hence not a unit.

This residue condition is necessary but should not be recorded as sufficient
without another proof.  The proof text also assumes that alternating-trail
switches can realize every residue prescription inside a component.  That is
a separate exchange-connectivity or bounded `b`-matching assertion, and it is
not supplied by the global hypotheses `deg_X = a`, `m | deg_Y`, and
`m | |X|`.

The likely salvage route is not a new universal balancing lemma over arbitrary
incidence multigraphs.  It is a Hamilton-incidence version tailored to the
splitting lemma, using the extra facts that:

- for each left vertex `x`, the adjacent right vertices are distinct Hamilton
  cycles, since a Hamilton cycle has only one outgoing arc at `x`;
- each right degree is the number of `i`-direction arcs in a Hamilton cycle,
  hence is positive and divisible by `m`;
- any component-level residue prescription must be proved realizable by an
  explicit switching, flow, or orientation argument.

For odd `m`, the CRT claim used in the proof remains useful: every residue
modulo `m` is a sum of two units.  Thus components with enough right-side
freedom have no purely arithmetic obstruction.  What remains is the structural
realization theorem for the special incidence graphs arising from Hamilton
decompositions.

## Replicated Shortcut Status - 2026-06-19

The revised shortcut proof replaces arbitrary incidence graphs by replicated
blocks.  In Lean this is now recorded by:

- `OddMultitori.ReplicatedSelection`;
- `OddMultitori.ReplicatedBalancingLemmaGoal`;
- `OddMultitori.MFiberedSplittingLemmaGoal`;
- `OddMultitori.MFiberedSplittingFromReplicatedBalancingGoal`.
- Local replicated block-choice infrastructure now closed in Lean:
  `OddMultitori.ReplicatedBlockChoice`,
  `OddMultitori.replicatedBlockColumnDegree`,
  `OddMultitori.ReplicatedBlockResiduePattern`,
  `OddMultitori.subtypeTrueEquiv`,
  `OddMultitori.fintype_card_subtype_true`,
  `OddMultitori.subtypeFalseEquiv`,
  `OddMultitori.fintype_card_subtype_false`,
  `OddMultitori.pairFiller_exists`,
  `OddMultitori.subsetFiller_exists`,
  `OddMultitori.pairTransferChoice`,
  `OddMultitori.pairTransferChoice_subset`,
  `OddMultitori.pairTransferChoice_card`,
  `OddMultitori.pairTransferChoice_q_card`,
  `OddMultitori.pairTransferChoice_p_card`,
  `OddMultitori.coprime_m_sub_of_coprime`,
  `OddMultitori.pairTransferChoice_q_coprime`,
  `OddMultitori.pairTransferChoice_p_coprime`,
  `OddMultitori.pairTransferChoice_inactive_dvd`, and
  `OddMultitori.pairResiduePattern_nonempty`.
- The unary pair-transfer reservoir is packaged as
  `OddMultitori.pairTransferBlockChoice_exists`: for distinct columns `p,q`
  and any unit `u <= m`, a replicated block can give column counts `m-u`
  and `u`, with both counts coprime to `m`.
  The stronger packaged form
  `OddMultitori.pairResiduePatternWithUnit_exists` also records the inactive
  columns as zero modulo `m`, which is the exact unary-edge tool needed by the
  top-down tree assignment.  The wrapper
  `OddMultitori.pairResiduePatternWithZModUnit_exists` gives the same unary
  transfer directly as `+u` at the child and `-u` at the parent in `ZMod m`.
- The triple reservoir `(1,1,m-2)` is also closed in Lean:
  `OddMultitori.tripleFiller_exists`,
  `OddMultitori.tripleTransferChoice`,
  `OddMultitori.tripleTransferChoice_subset`,
  `OddMultitori.tripleTransferChoice_card`,
  `OddMultitori.tripleTransferChoice_p_card`,
  `OddMultitori.tripleTransferChoice_q_card`,
  `OddMultitori.tripleTransferChoice_r_card`,
  `OddMultitori.coprime_m_sub_two_of_odd`,
  `OddMultitori.tripleTransferChoice_r_coprime`,
  `OddMultitori.tripleTransferChoice_inactive_dvd`,
  `OddMultitori.tripleTransferBlockChoice_exists`, and
  `OddMultitori.tripleResiduePattern_nonempty`.
  The exact-degree packaged form
  `OddMultitori.tripleResiduePatternWithDegrees_exists` records the active
  degrees `1,1,m-2` together with inactive zero-residue columns.  The wrapper
  `OddMultitori.tripleResiduePatternWithZModDegrees_exists` records this as
  `1,1,-2` in `ZMod m`.
- Active-set pair/triple cover infrastructure is now closed in Lean:
  `OddMultitori.nat_pair_or_pair_plus_triple`,
  `OddMultitori.finsetListUnion`,
  `OddMultitori.PairTripleCover`,
  `OddMultitori.pairTripleCover_of_card_two`,
  `OddMultitori.pairTripleCover_of_card_three`,
  `OddMultitori.PairTripleCover.cons`, and
  `OddMultitori.pairTripleCover_exists`.
- `OddMultitori.PairTripleCover` now includes the necessary row-count
  invariant
  `(pieces.map (fun P => P.card / 2)).sum = S.card / 2`.  This matters:
  arbitrary covers with multiple triple pieces do not preserve row size under
  naive partial-piece union.
- The partial-piece assembly layer is closed in Lean:
  `OddMultitori.PartialBlockChoice`,
  `OddMultitori.partialPairChoice_nonempty`,
  `OddMultitori.card_triple_of_ne`,
  `OddMultitori.partialTripleChoice_nonempty`,
  `OddMultitori.partialChoice_of_pairTriple_piece`,
  `OddMultitori.PartialListChoice`,
  `OddMultitori.partialListChoice_nil`,
  `OddMultitori.partialListChoice_cons`,
  `OddMultitori.partialListChoice_of_pairTriplePieces`,
  `OddMultitori.partialChoice_of_pairTripleCover`, and
  `OddMultitori.partialBlockChoice_empty`.
- The local arbitrary-active-set target is now closed:
  `OddMultitori.PairTripleCoverAssemblyGoal` is proved by
  `OddMultitori.pairTripleCoverAssemblyGoal_closed`, and
  `OddMultitori.LocalSubsetResiduePatternGoal` is proved by
  `OddMultitori.localSubsetResiduePatternGoal_closed`.  The direct base cases
  `OddMultitori.localSubsetResiduePattern_card_two` and
  `OddMultitori.localSubsetResiduePattern_card_three` remain as separately
  checked sanity lemmas.  The idle block pattern
  `OddMultitori.replicatedBlockResiduePattern_empty_nonempty` is also closed.
- The local residue-pattern-to-`ZMod` interface is now closed:
  `OddMultitori.replicatedBlockResiduePattern_active_isUnit` and
  `OddMultitori.replicatedBlockResiduePattern_inactive_zmod_eq_zero`.
  This lets the remaining global construction reason directly in `ZMod m`.
  The newer contribution lemmas
  `OddMultitori.replicatedBlockResiduePattern_zmod_eq_if_active` and
  `OddMultitori.replicatedBlockResiduePattern_sum_zmod_eq_active_sum` show
  that inactive block columns contribute zero to the global `ZMod` sum, so the
  final construction can be stated using only active-set contributions.
- The incidence graph groundwork for the remaining finite hypergraph proof is
  now present:
  `OddMultitori.IncidenceVertex`,
  `OddMultitori.replicatedIncidenceGraph`,
  `OddMultitori.replicatedIncidenceGraph_y_has_neighbor`,
  `OddMultitori.replicatedIncidenceGraph_block_has_two_neighbors`, and
  `OddMultitori.replicatedIncidenceGraph_reachable_y_rep`.  Component-level
  wrappers are also closed:
  `OddMultitori.replicatedIncidenceComponent_has_y`,
  `OddMultitori.replicatedIncidenceComponent_exists_isTree_le`,
  `OddMultitori.replicatedIncidenceTree_adj_val`,
  `OddMultitori.replicatedIncidenceTree_not_adj_left_left`,
  `OddMultitori.replicatedIncidenceTree_not_adj_right_right`,
  `OddMultitori.replicatedIncidenceTree_adj_right_eq_left`,
  `OddMultitori.replicatedIncidenceTree_adj_left_eq_right`,
  `OddMultitori.replicatedIncidenceComponent_block_has_two_y_neighbors`,
  `OddMultitori.replicatedIncidenceComponent_y_has_block_neighbor`,
  `OddMultitori.replicatedIncidenceComponent_has_other_y`, and
  `OddMultitori.replicatedIncidenceComponent_rooted_tree_exists`.  The stronger
  package `OddMultitori.replicatedIncidenceComponent_rooted_tree_with_tree_neighbor_exists`
  is also closed: it returns a rooted spanning tree together with an actual
  tree-neighbour block of the root.  The still stronger package
  `OddMultitori.replicatedIncidenceComponent_rooted_tree_with_branch_exists`
  is closed as well: it chooses a root-child block which has a non-root
  left-child in the tree.  These
  lemmas formalize the bipartite graph used for component-tree extraction,
  show that every block vertex has at least two left neighbours, show that
  every connected component has a left-side representative, show that a rooted
  component has another left vertex available, and package each component with
  a rooted spanning tree and a usable root branch.
- Rooted-tree orientation infrastructure is now closed:
  `OddMultitori.IsRootParent`,
  `OddMultitori.connected_exists_rootParent`,
  `OddMultitori.rootParent_spec`,
  `OddMultitori.rootParent_adj`,
  `OddMultitori.rootParent_dist_add_one`,
  `OddMultitori.rootParent_dist_lt`,
  `OddMultitori.isRootParent_unique`,
  `OddMultitori.rootParent_eq_of_isRootParent`,
  `OddMultitori.incidenceRootParent_left_eq_right`,
  `OddMultitori.incidenceRootParent_right_eq_left`,
  `OddMultitori.incidenceYParentBlock_exists`,
  `OddMultitori.incidenceBlockParentY_exists`,
  `OddMultitori.incidenceYParentBlock_unique`, and
  `OddMultitori.incidenceBlockParentY_unique`.  These lemmas orient a
  connected tree by distance from the root, verify that the parent of a
  left incidence vertex is a block while the parent of a block incidence
  vertex is a left vertex, and prove the parent is unique in the tree.
- Finite child-set infrastructure for the top-down assignment is now closed:
  `OddMultitori.rootChildrenFinset`,
  `OddMultitori.mem_rootChildrenFinset`,
  `OddMultitori.incidenceBlockChildren`,
  `OddMultitori.mem_incidenceBlockChildren`,
  `OddMultitori.incidenceBlockChildren_mem_incidence`,
  `OddMultitori.incidenceYChildren`,
  `OddMultitori.mem_incidenceYChildren`, and
  `OddMultitori.incidenceYChildren_mem_incidence`,
  `OddMultitori.incidenceYChildren_subset`,
  `OddMultitori.incidenceYChildren_card_le`,
  `OddMultitori.incidenceUnaryBlockChildren`,
  `OddMultitori.mem_incidenceUnaryBlockChildren`,
  `OddMultitori.incidenceUnaryBlockChildren_subset_blockChildren`,
  `OddMultitori.incidenceUnaryBlockChildren_block_mem_component`,
  `OddMultitori.incidenceUnaryBlockChildren_parent`,
  `OddMultitori.incidenceUnaryBlockChildren_child_card_eq_one`,
  `OddMultitori.incidenceUnaryBlockChildren_parentY_unique`,
  `OddMultitori.incidenceUnaryBlockChildren_parent_dist_lt_child`,
  `OddMultitori.incidenceBlockChildren_parentY_unique`,
  `OddMultitori.incidenceYChildren_parentBlock_unique`,
  `OddMultitori.root_not_mem_incidenceYChildren`, and
  `OddMultitori.incidenceYChildren_mem_of_root_branch`.  These are the finite
  sets over which the eventual unary child-transfer sums will be indexed, and
  Lean now verifies that a root-block-child branch really contributes a
  child in the rooted orientation.  The unary projection lemmas now also
  expose the parent relation, the unique-child cardinality, parent uniqueness,
  and the strict root-distance increase from the parent `Y` vertex to the
  unary child `Y` vertex.
- The older root branch pair reservoir is closed by
  `OddMultitori.rootBranchPairResiduePattern_nonempty`: if the chosen
  root-child block has a non-root left-child in the rooted tree, the active
  pair `{root, child}` already has an assembled replicated residue pattern.
  The stronger root-block reservoir now needed by the shortcut is also closed:
  `OddMultitori.incidenceRootBlockResiduePattern_nonempty` handles the active
  set `{root} ∪ children(rootBlock)`, and
  `OddMultitori.incidenceRootBlockResiduePattern_nonempty_of_branch` supplies
  the nonempty-child hypothesis from an actual root branch.
- The block-case local reservoirs are now packaged for the rooted tree:
  `OddMultitori.incidenceMultiChildResiduePattern_nonempty` handles any block
  with at least two left-children,
  `OddMultitori.finset_card_zero_or_one_or_two_le` supplies the finite child
  count split, `OddMultitori.incidenceZeroOrMultiChildResiduePattern_nonempty`
  packages the zero-child and multi-child cases together,
  `OddMultitori.incidenceUnaryChild_singleton` extracts the unique child in
  the unary case, and
  `OddMultitori.incidenceChildTransferResiduePatternWithZModUnit_exists`
  gives the unary transfer pattern from the block parent to a chosen child for
  any unit residue.  The finite-child packaging
  `OddMultitori.incidenceChildTransferPatternsWithUnitLabels_exists` now
  chooses unit labels for every child in a finite child set and packages the
  corresponding unary transfer patterns.  The top-down direction needed for
  the final proof is also now packaged:
  `OddMultitori.incidenceUnaryBlockResiduePatternWithZModUnit_exists` handles
  a single unary child block with a prescribed unit label, and
  `OddMultitori.incidenceUnaryBlockTransferPatternsWithUnitLabels_exists`
  chooses unit labels for all unary child blocks of a fixed `Y` vertex and
  proves that the parent contribution remains a unit after subtracting those
  transfers.  The generalized
  `OddMultitori.incidenceUnaryBlockTransferPatternsWithUnitLabelsOn_exists`
  handles any finite subset of those unary child blocks, and
  `OddMultitori.incidenceUnaryBlockTransferPatternsExceptWithUnitLabels_exists`
  specializes this to all unary child blocks except one distinguished block.
  This is the form needed at the root, where the chosen root block `α0` is
  handled by the root-block reservoir and must not be treated again as an
  ordinary unary child block.  The helper
  `OddMultitori.classicalFinsetErase` packages this exclusion without adding a
  `DecidableEq Block` assumption to the final goal.
- The same root-exception bookkeeping is now available directly at the
  component `Y`-vertex level.  `OddMultitori.componentYUnaryBlockChildrenExceptRoot`
  defines the outgoing unary child-block set, with `α0` removed only at the
  root, `OddMultitori.componentYUnaryBlockChildrenExceptRoot_subset` records
  that it is a subset of the ordinary unary child set, and
  `OddMultitori.componentYUnaryBlockChildrenExceptRoot_mem_of_parent` records
  the membership fact needed when a unary parent block is not the root
  exception.  The reusable unit-flow step is closed as
  `OddMultitori.componentYUnaryTransferPatternsExceptRootWithUnitLabels_exists`;
  its simultaneous finite-choice version is
  `OddMultitori.componentYUnaryTransferPatternFamilyExceptRootWithUnitLabels_exists`.
  These theorems still require a compatible incoming unit-residue assignment;
  constructing that assignment by rooted-tree recursion remains the next
  substantive Lean obligation.
- The top-down incoming assignment is now exposed as the named recursion
  `OddMultitori.componentVertexFlowDataFamily`, and the existence wrapper
  `OddMultitori.componentVertexFlowDataFamily_exists` now returns that named
  family instead of duplicating an anonymous `WellFounded.fix`.  The closed case
  equations are:
  `OddMultitori.componentVertexFlowDataFamily_root_incoming`,
  `OddMultitori.componentVertexFlowDataFamily_rootBlock_incoming`,
  `OddMultitori.componentVertexFlowDataFamily_nonUnary_incoming`, and the
  choice-form unary equation
  `OddMultitori.componentVertexFlowDataFamily_unary_choice_incoming`.
  The external unary transport form is now closed as
  `OddMultitori.componentBlockActivePattern_unary_child_zmod_eq_flow_incoming`,
  after normalizing `OddMultitori.componentOrdinaryUnaryBlockDataChoice` to use
  the named block-parent choice.
- The unit arithmetic needed for the top-down tree assignment is now closed:
  `OddMultitori.zmod_primePower_isUnit_of_cast_ne_zero`,
  `OddMultitori.zmod_primePower_unit_split`,
  `OddMultitori.zmod_unit_split_of_odd`,
  `OddMultitori.zmod_unit_sub_sum_units`, and
  `OddMultitori.zmod_unit_sub_sum_units_finset`.  The last two theorems say
  that from any unit residue `r : ZMod m`, one can choose any finite number
  of unit child transfers while keeping `r - sum(children)` a unit.
- The final block-choice counting layer is closed:
  `OddMultitori.replicatedGlobalSelectedDegree_eq_sum` identifies the global
  `Sigma Block × Fin m` selected degree with the sum of per-block column
  degrees, and `OddMultitori.replicatedSelection_of_blockChoices` packages
  block choices plus the summed coprimality check as a
  `OddMultitori.ReplicatedSelection`.
- The incidence extraction needed to apply replicated balancing to an
  `m`-fibered decomposition is now closed:
  `OddMultitori.directionColorSet`,
  `OddMultitori.directionColorSet_card`,
  `OddMultitori.fiberDirectionColorSet`,
  `OddMultitori.fiberDirectionColorSet_eq`,
  `OddMultitori.fiberDirectionColorSet_card`,
  `OddMultitori.color_uses_direction_exists`, and
  `OddMultitori.fiberDirectionColorSet_no_isolated`.  In particular, Lean now
  verifies the two key hypotheses for the extracted incidence hypergraph:
  every row has exactly `a` neighbours in the split direction, and every
  Hamilton colour uses that direction somewhere.
- The list-context bookkeeping for the split coordinate is closed:
  `OddMultitori.contextSplitDir`,
  `OddMultitori.contextSplitDir_get`, and
  `OddMultitori.replicatedBalancing_for_contextSplitDirection`.
- The carry arithmetic needed by the cyclic lift is closed:
  `OddMultitori.replicatedSelection_zmod_sum_indicator_eq_selectedDegree`,
  `OddMultitori.replicatedSelection_indicator_sum_isUnit`, and
  `OddMultitori.replicatedSelection_vertex_indicator_sum_isUnit`.  These
  identify the `ZMod m` carry sum over the old vertex set with the selected
  degree supplied by replicated balancing, hence prove that the carry is a
  unit.
- The Hamiltonicity part of the cyclic lift is now closed abstractly:
  `OddMultitori.replicatedSelection_liftedColor_singleCycle` applies the
  repository's skew-product holonomy theorem to prove that each lifted colour
  is a single Hamilton cycle whenever the replicated selection is available.
- The vertex-coordinate bookkeeping for the cyclic lift is now closed:
  `OddMultitori.finContractSplitEquiv` proves the generic equivalence
  `(Fin (n+1) -> ZMod m) ~= (Fin n -> ZMod m) × ZMod m` obtained by
  contracting adjacent child coordinates by addition and retaining the second
  child as the sheet coordinate.  The list-context wrapper
  `OddMultitori.contextSplitVertexEquiv` specializes this to
  `left ++ b :: c :: right` versus `left ++ (b+c) :: right`.
  The four basis-step conjugacy lemmas
  `OddMultitori.contextSplitVertexEquiv_add_firstChild`,
  `OddMultitori.contextSplitVertexEquiv_add_secondChild`,
  `OddMultitori.contextSplitVertexEquiv_add_oldBefore`, and
  `OddMultitori.contextSplitVertexEquiv_add_oldAfter` are also closed.
- The local marked/unmarked colour bookkeeping needed for the split child
  arc-copy partition is now closed:
  `OddMultitori.markedColorSet`,
  `OddMultitori.markedColorSet_subset_directionColorSet`,
  `OddMultitori.markedColorSet_card`,
  `OddMultitori.unmarkedColorSet`,
  `OddMultitori.unmarkedColorSet_card`,
  `OddMultitori.markedColorSet_card_contextSplit`, and
  `OddMultitori.unmarkedColorSet_card_contextSplit`.  Thus Lean now verifies
  that each old vertex has exactly `a/2` marked colours and `(a+1)/2`
  unmarked colours in the split direction.
- The local copy-index inverses for the two split child directions are now
  closed:
  `OddMultitori.finsetSubtypeEquivOfCard`,
  `OddMultitori.markedColorCopyEquiv`, and
  `OddMultitori.unmarkedColorCopyEquiv`.  These give the noncomputable
  bijections from child copy indices to the marked/unmarked old colours at
  each vertex.
- The colour-label transport layer is now closed:
  `OddMultitori.ColoredDecomposition`,
  `OddMultitori.decompositionOfColored`, and
  `OddMultitori.hasDecomposition_of_colored` allow the cyclic lift to keep
  old arc labels as colour labels and later convert back to the standard
  `Arc newParts` interface.
- The old/new arc-label cardinality bookkeeping is now closed:
  `OddMultitori.arc_card_eq_sum`,
  `OddMultitori.arc_card_eq_sum_context_old_new`, and
  `OddMultitori.oldNewArcEquiv`.
- The two child split direction constructors are now closed:
  `OddMultitori.contextSplitFirstDir`,
  `OddMultitori.contextSplitSecondDir`,
  `OddMultitori.firstChildArc`, and
  `OddMultitori.secondChildArc`.
- The non-split direction and arc transports are now closed:
  `OddMultitori.oldDirOfNewBefore`,
  `OddMultitori.oldDirOfNewAfter`,
  `OddMultitori.newDirOfOldBefore`,
  `OddMultitori.newDirOfOldAfter`,
  `OddMultitori.newArcOfOldBefore`,
  `OddMultitori.newArcOfOldAfter`,
  `OddMultitori.oldArcOfNewBefore`, and
  `OddMultitori.oldArcOfNewAfter`, together with the reconstruction lemmas
  for before/after arcs and first/second child arcs.
- The actual cyclic-lift colour map and ordinary decomposition are now closed:
  `OddMultitori.splitLiftColorArc`,
  `OddMultitori.splitLiftColorArc_edgePartition`,
  `OddMultitori.splitLiftCarry`,
  `OddMultitori.splitLiftColorArc_step_conj`,
  `OddMultitori.splitLiftColorArc_colorHamiltonian`,
  `OddMultitori.splitLiftColoredDecomposition`,
  `OddMultitori.splitLiftDecomposition`, and
  `OddMultitori.hasDecomposition_of_splitLiftSelection`.
- Replicated balancing is now connected to the ordinary split decomposition:
  `OddMultitori.hasDecomposition_contextSplit_of_replicatedBalancing` proves
  that an `m`-fibered old decomposition plus the replicated balancing lemma
  yields an ordinary Hamilton decomposition of the split multitorus.
- The lifted `m`-fibered invariant is now closed:
  `OddMultitori.splitLiftBlockEquiv`,
  `OddMultitori.splitLiftColorArc_fst_sheet_eq`,
  `OddMultitori.splitLiftDecomposition_sameDirectionColors`,
  `OddMultitori.splitLiftMFiberedDecomposition`, and
  `OddMultitori.hasMFiberedDecomposition_contextSplit_of_replicatedBalancing`.
  Consequently `OddMultitori.mFiberedSplittingFromReplicatedBalancingGoal`
  proves the full bridge
  `OddMultitori.MFiberedSplittingFromReplicatedBalancingGoal`.
- The final theorem spine has been shortened:
  `OddMultitori.oddDirectedTorusGoal_of_replicated_balancing_closedLift`
  now needs only `OddMultitori.ReplicatedBalancingLemmaGoal`, and
  `OddMultitori.oddDirectedTorusGoal_of_replicated_blockChoiceConstruction`
  reduces the final directed-torus theorem to
  `OddMultitori.ReplicatedBlockChoiceConstructionGoal`.
- The remaining constructive balancing core is now isolated most sharply as
  `OddMultitori.ReplicatedResiduePatternUnitAssignmentGoal`: choose active
  sets and already-closed local residue patterns so that every right vertex
  receives a unit active contribution in `ZMod m`.  This implies
  `OddMultitori.ReplicatedBlockChoiceUnitConstructionGoal`, which in turn is
  equivalent to the older coprimality formulation
  `OddMultitori.ReplicatedBlockChoiceConstructionGoal`.  The bridge
  `OddMultitori.replicatedBlockChoiceUnitConstructionGoal_of_residuePatternUnitAssignment`
  performs the active-sum-to-degree-sum conversion, the bridge
  `OddMultitori.replicatedBlockChoiceConstructionGoal_of_unit` converts the
  `ZMod` unit formulation to the original coprimality formulation, and
  `OddMultitori.replicatedBalancingLemmaGoal_of_blockChoiceConstruction`
  proving that this construction goal implies
  `OddMultitori.ReplicatedBalancingLemmaGoal`.
- The global residue goal is now reduced to a component-local formulation:
  `OddMultitori.ComponentResiduePatternUnitAssignmentGoal`.  This goal assigns
  active sets and local residue patterns component by component, with all
  blocks outside the component forced idle.  The bridge
  `OddMultitori.replicatedResiduePatternUnitAssignmentGoal_of_component` is
  closed in Lean.  Thus the remaining balancing construction no longer needs
  to reason about different connected components simultaneously.
- The component-local goal is further reduced to a rooted-tree formulation:
  `OddMultitori.RootedTreeResiduePatternUnitAssignmentGoal`.  The bridge
  `OddMultitori.componentResiduePatternUnitAssignmentGoal_of_rootedTree` is
  closed, and the final theorem wrapper
  `OddMultitori.oddDirectedTorusGoal_of_replicated_rootedTreeResiduePatternUnitAssignment`
  records the general rooted-tree spine: this one rooted-tree assignment
  theorem implies the odd directed torus theorem.
- A sharper branch-rooted formulation is now also recorded:
  `OddMultitori.RootedBranchResiduePatternUnitAssignmentGoal`.  Its bridge
  `OddMultitori.componentResiduePatternUnitAssignmentGoal_of_rootedBranch`
  uses the already-closed branch extraction theorem
  `OddMultitori.replicatedIncidenceComponent_rooted_tree_with_branch_exists`,
  and the final wrapper
  `OddMultitori.oddDirectedTorusGoal_of_replicated_rootedBranchResiduePatternUnitAssignment`
  is closed.  This is now the Lean target that most accurately matches the
  corrected shortcut proof, because the root block is guaranteed to have a
  non-root child.
- The branch-rooted target has also been reduced to a component-subtype form:
  `OddMultitori.RootedBranchComponentBlockResiduePatternUnitAssignmentGoal`.
  The bridge
  `OddMultitori.rootedBranchResiduePatternUnitAssignmentGoal_of_componentBlock`
  is closed in Lean.  It extends component-block patterns to all blocks by
  idle patterns and proves the full `Block` sum equals the component-subtype
  sum using `Finset.sum_filter` and `Finset.sum_subtype`.  Thus the remaining
  construction only needs to assign patterns to block vertices actually lying
  in the chosen connected component.  The matching finite left-vertex subtype
  `OddMultitori.ComponentY` is also now available for the eventual
  distance-recursive construction over component `Y` vertices, with
  `OddMultitori.componentYVertex`, `OddMultitori.componentYRootDist`, and
  `OddMultitori.componentYRootDist_lt_of_unary_child` packaging the rooted
  distance measure and its strict increase along unary child transfers.  The
  stronger wrapper `OddMultitori.componentYRootDist_lt_of_parentBlock_child`
  records the same strict increase for any parent-block-to-child step, and
  `OddMultitori.componentBlockParentY_exists` /
  `OddMultitori.componentYParentBlock_exists` expose rooted parents on both
  sides as component subtypes.  The component-child finset
  `OddMultitori.componentBlockYChildren` is now available, with
  `OddMultitori.mem_componentBlockYChildren`,
  `OddMultitori.componentBlockYChildren_mk_mem`,
  `OddMultitori.componentBlockYChildren_dist_lt_of_parent`, and
  `OddMultitori.componentBlockYChildren_eq_of_card_one` packaging membership,
  component lifting, distance increase, and uniqueness in the unary case.  The
  component-level incoming source split is now isolated as
  `OddMultitori.ComponentIncomingSource`, and
  `OddMultitori.componentIncomingSource_exists` proves that every component
  `Y`-vertex falls into exactly the kind of case needed by the top-down proof:
  root, distinguished root block, non-unary parent block, or unary transfer
  from its parent `Y`-vertex.  These cases now also have a contribution layer:
  `OddMultitori.ComponentIncomingContribution` relates a source case to its
  actual `ZMod m` incoming value from the chosen local patterns/labels, and
  `OddMultitori.componentIncomingContribution_exists_of_source` proves that
  every such source supplies a unit value.  The source-specific wrappers
  `OddMultitori.componentRootPattern_root_isUnit`,
  `OddMultitori.componentRootPattern_child_isUnit`,
  `OddMultitori.componentNonUnaryPattern_child_isUnit`, and
  `OddMultitori.componentUnaryPairResiduePatternWithZModUnit_exists` are closed
  and will feed the final sum proof.
- The ordinary-unary and top-down flow layers are now closed in Lean:
  `OddMultitori.ComponentOrdinaryUnaryBlockData` packages a non-root unary
  block with its parent `Y` vertex, unique child `Y` vertex, and membership in
  the parent vertex's ordinary-unary outgoing set;
  `OddMultitori.componentOrdinaryUnaryBlockData_exists` constructs this data
  from the rooted tree, and
  `OddMultitori.componentOrdinaryUnaryBlockData_pair_subset` proves the active
  pair `{parent, child}` is contained in the block neighbour set.  The local
  flow package `OddMultitori.ComponentYFlowData` records the unit labels,
  final parent residue, and transfer patterns produced at one `Y` vertex;
  `OddMultitori.componentYFlowData_exists` and
  `OddMultitori.componentYFlowDataFamily_exists` close the finite-choice
  wrappers.  The bridge
  `OddMultitori.componentOrdinaryUnaryBlockData_flowTransferPattern_exists`
  realizes a parent flow label on the actual ordinary-unary block pair.
  Finally, `OddMultitori.ComponentVertexFlowData` and
  `OddMultitori.componentVertexFlowDataFamily_exists` close the well-founded
  top-down recursion over `OddMultitori.componentYRootDist`.  The recursion is
  now also exposed as the named definition
  `OddMultitori.componentVertexFlowDataFamily`, so `WellFounded.fix_eq` can be
  used in downstream compatibility proofs.  The root, root-block child, and
  non-unary incoming equations are closed as
  `OddMultitori.componentVertexFlowDataFamily_root_incoming`,
  `OddMultitori.componentVertexFlowDataFamily_rootBlock_incoming`, and
  `OddMultitori.componentVertexFlowDataFamily_nonUnary_incoming`.
  The unary incoming equation is also now closed in the form needed downstream:
  `OddMultitori.componentVertexFlowDataFamily_unary_choice_incoming` gives the
  recursion equation at the named parent choice, and
  `OddMultitori.componentBlockActivePattern_unary_child_zmod_eq_flow_incoming`
  transports the active unary-child contribution all the way to
  `(flow y).incoming`.
- The component-block assignment skeleton is now closed up to the final
  contribution-sum unit proof.  `OddMultitori.componentOrdinaryUnaryBlockDataChoice`
  and `OddMultitori.componentBlockActiveSet` define the active set for each
  component block by cases: root block, ordinary unary block, or child-set
  block.  `OddMultitori.componentBlockActiveSet_subset` proves every such
  active set lies in the corresponding neighbour set.
  The case rewrite and membership lemmas
  `OddMultitori.componentBlockActiveSet_root_eq`,
  `OddMultitori.componentBlockActiveSet_nonunary_eq`,
  `OddMultitori.componentBlockActiveSet_unary_eq`,
  `OddMultitori.mem_componentBlockActiveSet_root`,
  `OddMultitori.mem_componentBlockActiveSet_nonunary`,
  `OddMultitori.mem_componentBlockActiveSet_unary`,
  `OddMultitori.componentBlockActiveSet_mem_of_ordinary_parent`, and
  `OddMultitori.componentBlockActiveSet_mem_of_unary_child` are also closed.
  The ordinary-unary choice is pinned down by
  `OddMultitori.componentOrdinaryUnaryBlockDataChoice_parent_eq_of_mem` and
  `OddMultitori.componentOrdinaryUnaryBlockDataChoice_child_eq_of_child`, and
  the child-side exact degree rewrite
  `OddMultitori.componentOrdinaryUnaryBlockPattern_child_zmod_of_child` is
  available for incoming unary contributions.  The parent-side dependent
  transport is now also closed as
  `OddMultitori.componentOrdinaryUnaryBlockPattern_parent_zmod_of_mem`.
  `OddMultitori.componentBlockActivePattern_exists` and
  `OddMultitori.componentBlockActivePatternFamily_exists` choose local residue
  patterns for every active set, using the top-down flow labels in the
  ordinary-unary case.  The family now uses the concrete
  `OddMultitori.componentBlockActivePattern` rather than an opaque
  `Classical.choice`, and the case readout lemmas
  `OddMultitori.componentBlockActivePattern_root_zmod`,
  `OddMultitori.componentBlockActivePattern_root_child_zmod`,
  `OddMultitori.componentBlockActivePattern_nonunary_zmod`,
  `OddMultitori.componentBlockActivePattern_unary_child_zmod`, and
  `OddMultitori.componentBlockActivePattern_unary_parent_zmod` are closed.
  The source-specialized contribution wrappers are now closed too:
  `OddMultitori.componentBlockActivePattern_root_zmod_eq_flow_incoming`,
  `OddMultitori.componentBlockActivePattern_root_child_zmod_eq_flow_incoming`,
  `OddMultitori.componentBlockActivePattern_nonunary_zmod_eq_flow_incoming`,
  `OddMultitori.componentBlockActivePattern_unary_child_zmod_eq_flow_incoming`,
  and the aggregate source selector
  `OddMultitori.componentYIncomingBlock_active_zmod_eq_flow_incoming`.
  The ordinary-unary outgoing side is now packaged by
  `OddMultitori.componentYUnaryBlockChildrenExceptRoot_ne_rootBlock`,
  `OddMultitori.componentYUnaryBlockChildrenExceptRoot_active_zmod_eq_neg_flow_label`,
  and the source/outgoing disjointness lemma
  `OddMultitori.componentYIncomingBlock_not_mem_unaryChildrenExceptRoot`.
  `OddMultitori.componentBlockActiveSet_mem_source_or_unaryChild` classifies
  every active membership as either the unique incoming source block or one of
  the ordinary-unary child blocks of that `Y` vertex.  Finally,
  `OddMultitori.componentVertexFlowDataFamily_final_residue_isUnit` exposes the
  exact unit target
  `incoming(y) - sum(outgoing ordinary-unary labels)`.
  Finally,
  `OddMultitori.componentBlockActiveAssignmentSkeleton_exists` returns the
  `S`, `P`, and subset fields in essentially the same shape as
  `OddMultitori.RootedBranchComponentBlockResiduePatternUnitAssignmentGoal`.
  The final `forall y, IsUnit (active contribution sum at y)` field is closed
  by `OddMultitori.componentBlockActiveContribution_sum_eq_final_residue`.
- The final wrapper
  `OddMultitori.oddDirectedTorusGoal_of_replicated_rootedBranchComponentBlockResiduePatternUnitAssignment`
  records that this component-subtype theorem alone implies the final odd
  directed-torus target.

Mathematical verdict:

- The previous parallel-incidence counterexample does not refute the replicated
  lemma.  The new hypothesis is stronger: each block has `m` simple rows with
  the same neighbour set, represented as a finite set `A α` of size `a`.
- The local block patterns `(1,m-1)` and `(1,1,m-2)` are now machine-checked
  as standalone reservoirs for odd `m`.  They are also packaged as residue
  patterns: active columns receive selected degree coprime to `m`, while
  inactive block columns receive selected degree divisible by `m`.
- Every active set `S` with `|S| >= 2` is now machine-checked to have a
  row-balanced disjoint cover by two- and three-element pieces, and the closed
  piece reservoirs are assembled into one row choice for the whole block.
- The incidence-tree argument is plausible and appears to remove the earlier
  component-sum obstruction: unary hyperedges can pass freely chosen units
  downward while subtracting them from the parent, and the required CRT
  two-units arithmetic is now machine-checked.
- The replicated shortcut is now a closed Lean proof route.  The final
  component-block obligation
  `OddMultitori.RootedBranchComponentBlockResiduePatternUnitAssignmentGoal` is
  proved by
  `OddMultitori.rootedBranchComponentBlockResiduePatternUnitAssignmentGoal_closed`.
  The last missing finite-sum step is closed by
  `OddMultitori.componentBlockActiveContribution_eq_source_plus_unary`,
  `OddMultitori.componentBlockActiveContribution_sum_eq_final_residue`, and
  the dependent reindexing lemma
  `OddMultitori.componentBlock_sum_dite_val_mem_eq_subtype_sum`.
- No lift-side decomposition obligation remains: the ordinary cyclic lift, the
  transported fiber-block equivalence, the direction-colour constancy
  statement, the replicated balancing bridge, and the component residue
  assignment are all closed in Lean.

Thus the revised route should be classified as **machine-verified in Lean** for
the saved theorem spine.  The closed final theorem is
`OddMultitori.oddDirectedTorusGoal_replicated_shortcut_closed`, which proves
`OddMultitori.OddDirectedTorusGoal` without any remaining balancing or
splitting assumptions.

Saved as explicit Lean proof obligations:

- `OddMultitori.SplittingLemmaGoal`: this must now be proved by a corrected
  argument, not by the false balancing lemma as written.
- `OddMultitori.SplittingFromBalancingGoal`: retained only as a placeholder for
  a corrected balancing-to-splitting replacement.
- `OddMultitori.ReplicatedBlockChoiceUnitConstructionGoal`,
  `OddMultitori.ReplicatedResiduePatternUnitAssignmentGoal`,
  `OddMultitori.ComponentResiduePatternUnitAssignmentGoal`,
  `OddMultitori.RootedTreeResiduePatternUnitAssignmentGoal`,
  `OddMultitori.RootedBranchResiduePatternUnitAssignmentGoal`, and
  `OddMultitori.RootedBranchComponentBlockResiduePatternUnitAssignmentGoal`:
  these remain useful named intermediate targets, but the branch-component
  target is now proved by
  `OddMultitori.rootedBranchComponentBlockResiduePatternUnitAssignmentGoal_closed`,
  and the final theorem no longer assumes them.

The final saved theorem spine is:

```lean
OddMultitori.oddDirectedTorusGoal_of_balancing :
  SplittingFromBalancingGoal ->
  BalancingLemmaGoal ->
  StandardBridgeGoal ->
  OddDirectedTorusGoal
```

and, if the splitting lemma is supplied directly:

```lean
OddMultitori.oddDirectedTorusGoal_of_splitting_closedBridge :
  SplittingLemmaGoal ->
  OddDirectedTorusGoal
```

The replicated shortcut is now closed without extra hypotheses:

```lean
OddMultitori.oddDirectedTorusGoal_replicated_shortcut_closed :
  OddDirectedTorusGoal
```

## Next Lean Targets

1. Prove `OddMultitori.PairTripleCoverAssemblyGoal` as a `Finset`
   construction.  **Done** by `OddMultitori.pairTripleCoverAssemblyGoal_closed`.
2. Prove the CRT unit-choice lemma.  **Done** by
   `OddMultitori.zmod_unit_split_of_odd` and
   `OddMultitori.zmod_unit_sub_sum_units`.
3. Prove the global block-choice counting assembly.  **Done** by
   `OddMultitori.replicatedGlobalSelectedDegree_eq_sum` and
   `OddMultitori.replicatedSelection_of_blockChoices`.
4. Prove
   `OddMultitori.RootedBranchComponentBlockResiduePatternUnitAssignmentGoal`.
   **Done** by
   `OddMultitori.rootedBranchComponentBlockResiduePatternUnitAssignmentGoal_closed`.
   The final contribution `Finset.sum` classification is closed by
   `OddMultitori.componentBlockActiveContribution_sum_eq_final_residue`.
5. Use the now-closed bridges
   `OddMultitori.rootedBranchResiduePatternUnitAssignmentGoal_of_componentBlock`,
   `OddMultitori.componentResiduePatternUnitAssignmentGoal_of_rootedBranch` and
   `OddMultitori.replicatedResiduePatternUnitAssignmentGoal_of_component` to
   obtain `OddMultitori.ReplicatedResiduePatternUnitAssignmentGoal`, then
   `OddMultitori.replicatedBlockChoiceUnitConstructionGoal_of_residuePatternUnitAssignment`
   supplies the block-choice construction automatically.  **Done** inside
   `OddMultitori.oddDirectedTorusGoal_replicated_shortcut_closed`.
6. Use the now-closed
   `OddMultitori.mFiberedSplittingFromReplicatedBalancingGoal` and
   `OddMultitori.oddDirectedTorusGoal_of_replicated_balancing_closedLift`
   spines.  **Done** by
   `OddMultitori.oddDirectedTorusGoal_replicated_shortcut_closed`.
