# Previous Paper Route Audit

Date: 2026-05-05

Purpose: record which proof routes were already plausible in earlier paper
versions, which parts were later superseded, and where the current Lean
development is ahead of the manuscript.

## Executive Verdict

Earlier versions already had the right global architecture, especially from v4
onward:

- finite seed dimensions;
- product/composite closure;
- high-modulus prefix-count branch;
- q = 1 Gale-Ryser/matching correction;
- small-modulus successor branch through base-tail Hall slack;
- Active Hall realization as the finite assignment theorem behind the
  base-tail branch.

The main correction is Appendix A.  The v7 trellis/Hoffman-Edmonds-Giles route
was a plausible manuscript-level route, but it is not safe as written.  The
current Lean development replaces that proof package by a concrete binary-layer
decomposition

```text
Sigma_ik = -2 + A_ik + 3 B_ik,
```

where `A` and `B` are zero-one layers.  This is the new proof-theoretic step
that the earlier paper versions did not explicitly contain.

## Source Map

The audit compares the following local sources.

| Source | Role in audit |
|---|---|
| `docs/PREFIX_COUNT_ODD_TORI_OVERHAULED_V2_20260503.md` | first broad v2 architecture and base-tail Hall-slack branch |
| `docs/PREFIX_COUNT_ODD_TORI_OVERHAULED_V4_ABSORPTION_20260504.md` | v4 proof spine and successor closure refactor |
| `/data/angel/repos/etc/prefix_count_odd_tori_overhauled_v7.tex` | v7 manuscript and Appendix A trellis/HEG proof attempt |
| `docs/GPT55_PRO_QGE2_INDICATOR_TO_FULL_SUPPORT_RESPONSE_20260504.md` | half-slack/level-cake correction for q >= 2 support |
| `docs/GPT55_PRO_QGE2_PROPER_CUT_RESPONSE_20260504.md` | ordinary-only closure target and warning against arbitrary row packing |
| `RoundComposite/PrefixCountHalfSlack.lean` | Lean bridge from ordinary seed closure to full support, and half-slack equivalence |
| `RoundComposite/FiniteHoffman/SignedTrellis.lean` | committed Lean binary-layer closure for q >= 2 |
| `RoundComposite/FiniteHoffman/EdgeColoring.lean` and `RoundComposite/ActiveHall.lean` | ActiveHall/de Werra adapters and remaining finite theorem endpoint |

The Lean file `RoundComposite/FiniteHoffman/SignedTrellis.lean` is now part of
the current branch.  The status judgments below refer to that committed local
branch state plus any explicitly noted dirty Goal 2 files in the shared
worktree.

## Timeline Verdict

| Stage | What was already plausible | What was missing or unsafe |
|---|---|---|
| v2 | Active Hall polytope, barycenter, universal residues, controlled rounding, base-tail Hall-slack branch. | q >= 2 signed matrix realization still a large external target; ActiveHall finite theorem not formalized. |
| v4 | Clean global proof spine: count branch for `m >= d`, q = 1 Gale-Ryser/matching correction, q >= 2 signed transportation, successor closure `b -> 2*b+1`. | q >= 2 signed transportation still treated as a named finite theorem; base-tail and ActiveHall still theorem endpoints. |
| v7 | Appendix A isolates signed-column decomposition and uses trellis objects instead of a box relaxation. | It invokes HEG/submodular-flow sufficiency through row-subset cuts. This is the dangerous step; arbitrary signed-column packing from row-subset cuts is false. |
| 2026-05-04 GPT responses | Correctly separates the half-slack bridge and warns not to prove arbitrary row packing. Recommends ordinary signed-seed closure as the actual target. | Still leaves the final ordinary integrality theorem as a black box or external HEG-style theorem. |
| Current Lean | Closes q >= 2 ordinary signed trellis through binary layers `-2 + A + 3B`, plus small `n = 4, 6` and uniform `n >= 8` cases. | ActiveHall/de Werra and parts of base-tail geometry/rounding remain separate large targets. |

## Detailed Findings

### 1. Global closure route

The v4 route was already close to the final intended proof architecture.  It
reduces all odd moduli and all dimensions to:

```text
D2, D3, D5, D7 seeds
product/composite closure
count branch for m >= d
successor closure b -> 2*b + 1
```

This replaced the earlier finite `d < 29` boundary worldview.  The v4 document
also records that the dispatcher theorem from these pieces to the final
all-dimensional endpoint was already Lean-closed in that stage.

Status: structurally correct and still the right top-level manuscript route.

### 2. q = 1 branch

The q = 1 branch was already plausibly solved in the older manuscript path by
ordinary bipartite zero-one degree realization, namely a Gale-Ryser style
plus-set construction plus a matching correction.  This is consistent with the
Lean direction where the q = 1 target-Hall data is no longer the main blocker.

Status: earlier route was plausible and remains compatible with the Lean proof
spine.

### 3. q >= 2 branch before the binary-layer proof

The v2/v4 documents identify the correct mathematical object: a signed matrix
with entries in `{ -2, -1, 1, 2 }`, prescribed row sums, and column sums
`-c_k` for `c_k in {1,2}`.  This is the correct target.

The problem is the proof package used later in v7.  Appendix A defines the
signed column family

```text
C_c(L) = { x in {-2,-1,1,2}^L : sum_i x_i = -c }
```

and uses a trellis to represent one column.  That is a good modeling step.
However, the proof then says that the row-subset cut inequalities are the
Hoffman-Edmonds-Giles cuts for the glued trellis instance and invokes an
integral submodular-flow theorem to obtain the decomposition.

This is not safe as a standalone argument.  The no-zero alphabet creates
integer holes.  In particular, arbitrary row vectors can satisfy the displayed
row-subset cuts without being decomposable into the signed columns.  The
correct theorem must remain restricted to the ordinary q >= 2 row shape, or
must use a stronger/concrete construction.

Status: the v7 route was plausible but should be replaced in the paper.

### 4. Half-slack bridge

The 2026-05-04 q >= 2 support response already gives the key correction:
arbitrary integer weights are handled by level-cake decomposition, and the
single missing value at the half level for the `c = 2` signed column is paid by
ordinary-row half slack.

Lean now reflects this as:

- `qge2SignedColumnSupport_one_ge_levelCapacity_sub_halfPenalty`;
- `qge2SignedColumnSupport_two_ge_levelCapacity_sub_halfPenalty`;
- `ordinaryQge2IndicatorToFullSupportGoal_of_signedSupportHalfPenalty`;
- `ordinaryQge2IndicatorToFullSupportGoal_of_internalHalfSlack`;
- the full-support/proper-cut equivalence around
  `ordinaryQge2SignedFullSupportTrellisGoal_iff_seedProperCutClosureGoal`.

This part is no longer just plausible.  It is the correct bridge between
ordinary indicator cuts and full integer-weight support inequalities.

Status: Lean is ahead of the paper; manuscript should present this as the
verified bridge, not as a generic Lovasz/base-polyhedron theorem.

### 5. Binary-layer closure

The current Lean development closes the remaining q >= 2 signed trellis field
by replacing the trellis/HEG integrality claim with a concrete two-layer
decomposition.  The key encoding is:

```lean
def qge2LayeredSignedEntry (A B : Nat) : Int :=
  -2 + (A : Int) + 3 * (B : Int)
```

When `A,B in {0,1}`, this gives exactly:

```text
(A,B) = (0,0) -> -2
(A,B) = (1,0) -> -1
(A,B) = (0,1) ->  1
(A,B) = (1,1) ->  2
```

The signed matrix problem is therefore reduced to two zero-one degree matrices
`A` and `B`, with shifted row/column equations:

```text
sum_k (A_ik + 3 B_ik)
  = qge2OrdinaryRowTarget_i + 2*(n-1),

sum_i (A_ik + 3 B_ik)
  = 2*n - c_k.
```

The current Lean route then supplies:

- `OrdinaryQge2BinaryLayerTrellisGoal`;
- `OrdinaryQge2BinaryLayerDegreeGoal`;
- `exists_qge2SignedFullSupportTrellisWitness_of_binaryLayerDegreeData`;
- uniform degree construction for `n >= 8`;
- special closures for `n = 4` and `n = 6`;
- final `ordinaryQge2SignedFullSupportTrellisGoal`;
- final `ordinaryQge2SignedSeedProperCutClosureGoal`.

Status: this is the decisive new proof path.  It should replace the Appendix A
HEG/submodular-flow paragraph.

### 6. Active Hall / de Werra

The Active Hall path was already plausible in v2/v4/v7.  The theorem shape is
standard: an active incidence system with row sums, column sums, and rectangle
Hall cuts should realize a symboling.  In Lean, the adapters are now quite
developed:

```text
CompatibleDeWerraGoal
  -> RawExactEdgeColoringGoal
  -> ExactEdgeColoringGoal
  -> HallRealizationGoal
```

and the zero-one matrix form has also been separated:

```text
RawZeroOneMatrixGoal
RawZeroOneMatrixGoal <-> HallRealizationGoal
RawZeroOneMatrixGoal <-> EraseLastHallCutsProperTokenQuotaSelectionGoal
```

However, the actual general finite compatible edge-colouring / de Werra quota
theorem is still not proved unconditionally in the local Lean source.

Status: earlier paper route remains plausible, but Lean has not closed the
central finite theorem.

### 7. Base-tail geometry and residue rounding

The base-tail idea was already present and mathematically coherent in v2/v4:
use a solved base dimension, expand through unit packets, introduce active tail
symbols, and solve active symboling by Hall slack plus residue-compatible
rounding.

The later corrections are important:

- the cylinder structure must remember active block/degree information, not
  only a direction map;
- residue rounding must explicitly use divisibility and nonnegativity
  hypotheses;
- primitive tail lifting should be stated through the lower-triangular/unit
  monodromy data, rather than as an informal base-tail bookkeeping claim.

Status: manuscript route is plausible but still needs theorem-shaped Lean
closure in the remaining geometry/rounding fields.

## Where the Paper Should Change

The largest manuscript change should be Appendix A.

Do not state or rely on:

```text
row-subset signed-column cuts imply arbitrary signed-column packing.
```

Do state:

```text
For the ordinary q >= 2 row targets, the signed matrix exists.
The proof proceeds by:
  1. indicator/full-support bridge with half-level slack;
  2. binary-layer encoding Sigma = -2 + A + 3B;
  3. zero-one degree realizations for A and B;
  4. small n = 4,6 checks and uniform n >= 8 construction.
```

The v7 trellis paragraph can still be kept as motivation for the signed-column
support function, but not as the closing integrality theorem.

## Lean Versus Manuscript

| Component | Manuscript status | Lean status |
|---|---|---|
| Top-level successor closure dispatcher | v4 route correct | endpoint adapters largely closed |
| q = 1 Gale-Ryser/matching correction | plausible and manuscript-friendly | no longer main blocker |
| q >= 2 half-slack support bridge | hinted by GPT response, not fully in paper | closed in Lean support files |
| q >= 2 signed integrality | v7 HEG route unsafe | current Lean closes by binary layers |
| ActiveHall/de Werra | plausible standard finite theorem | adapters closed, theorem itself open |
| Base-tail cylinder/rounding/lift | plausible but needs precise hypotheses | partially reduced, residual fields remain |

## Recommended Next Synchronization

1. Rewrite Appendix A around the binary-layer proof.
2. Keep the half-slack bridge as the official reason full integer-weight
   support inequalities are available.
3. Demote the v7 trellis/HEG paragraph to motivation or remove it.
4. Preserve the v4 global proof spine; it is still the cleanest top-level
   story.
5. Separate the remaining non-Appendix-A work into:
   - finite de Werra / compatible edge-colouring theorem;
   - controlled residue rounding inside the active Hall polytope;
   - base-tail cylinder and lower-triangular primitive lift assembly.

## Short Bottom Line

The earlier papers were not on the wrong global path.  They had the right
architecture and many of the right theorem boundaries.  The main incorrect or
unfinished point was the proof package for Appendix A.  Current Lean advances
the project by replacing that package with a concrete binary-layer construction
that is much more suitable both for the paper and for formalization.
