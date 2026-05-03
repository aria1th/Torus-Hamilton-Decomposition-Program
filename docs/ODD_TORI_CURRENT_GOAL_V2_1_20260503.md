# Odd-Modulus Tori Current Goal v2.1

Date: 2026-05-03.

This note records the revised goal after the `d < 29` boundary review.  The
finite boundary table is no longer part of the intended proof spine.  The main
Lean goal is now the all-dimensional odd-modulus theorem, reduced to two
uniform construction theorems.

## Final Theorem

Target endpoint:

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Mathematically, for every `d >= 2` and every odd `m >= 3`, the standard
directed torus

```text
Cay((ZMod m)^d, {e_0, ..., e_{d-1}})
```

has a directed Hamilton decomposition.

## Main Revision

The old boundary framing was:

```text
high branch + finite d < 29 boundary + later lifting
```

The current framing is:

```text
D2/product wrapper
+ odd-dimensional core
+ high-modulus prefix-count theorem
+ small-modulus Hall-slack packet-lift theorem
```

Thus the `d < 29` table is retained only as audit/regression evidence.  It
should not be imported by the main Lean theorem and should not be treated as a
required theorem-level hypothesis.

In particular, `(d,m) = (13,3)` is not a special leftover pair in the revised
spine.  It is covered by the uniform small-modulus pattern once the base-tail
Hall-slack packet-lift theorem is proved, using a solved seed-semigroup base
such as `b = 6 = 2 * 3`.

## Proof Spine

### 1. All-Dimensional Wrapper

Use the D2 seed and product lift to reduce every even dimension to a smaller
dimension.  Therefore the hard construction is the odd-dimensional core.

Lean artifact:

```lean
theorem RoundComposite.Concrete.standard_cayley_odd_uniform_all_dimensions_of_odd_core
```

Status: closed.

### 2. Odd-Dimensional Core

For odd `d >= 3`, split by small seed dimensions and the general branches.

Small odd dimensions:

```text
d = 3   D3 seed
d = 5   D5 seed
d = 7   D7 seed
d = 9   D3 * D3 product
d = 11  high branch for m >= 11, small branch from b = 5 for m < 11
```

For odd `d >= 13`:

```text
m >= d  high-modulus prefix-count theorem
m < d   small-modulus Hall-slack packet-lift theorem
```

Lean artifact:

```lean
theorem RoundComposite.Concrete.odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Status: conditional skeleton closed.

## Remaining Public Theorem Families

### A. High-Modulus Prefix-Count Theorem

Lean-facing goal:

```lean
def RoundComposite.Concrete.OddCoreHighModulusPrefixCountGoal : Prop :=
  forall {d m : Nat}, Odd d -> 5 <= d -> Odd m -> d <= m ->
    StandardCayleySolved d m
```

This should prove all odd `d >= 5` and odd `m >= d`.

Current reduction inside `RoundComposite/PrefixCount.lean`:

```lean
TransportQge2Goal
TransportQeq1Goal
AdmissiblePartsCountBranchGoal
admissiblePartsCountBranchGoal_of_transports
```

Lean bridge now recorded in `RoundComposite/OddCore.lean`:

```lean
PrefixCount.MatrixBalanced
PrefixCount.BalancedMatrixLayerRealizationGoal
PrefixCount.balancedMatrixLayerRealization_zero
PrefixCount.matrixBalanced_exists_positive_perm
PrefixCount.peelLayer
PrefixCount.peelLayer_balanced
PrefixCount.balancedMatrixLayerRealizationGoal
PrefixCount.MatrixAdmissible.toBalanced
PrefixCount.matrixLayerRealizationGoal_of_balanced
PrefixCount.matrixLayerRealizationGoal
PrefixCount.MatrixLayerRealizationGoal
PrefixCount.layerRealization_of_matrixLayerRealizationGoal
PrefixCountLayerRealizationGoal
PrefixCountGeometricCriterionGoal
prefixCountLayerRealizationGoal_of_balancedMatrixLayerRealization
prefixCountLayerRealizationGoal_of_matrixLayerRealization
prefixCountLayerRealizationGoal
oddCoreHighModulusPrefixCountGoal_of_parts_and_geometry
oddCoreHighModulusPrefixCountGoal_of_transports_and_geometry
odd_modulus_tori_all_dimensions_of_transports_geometry_and_small_packet_lift
PrefixCount.MarginTransportQge2Goal
PrefixCount.MarginTransportQeq1Goal
PrefixCount.transportQge2Goal_of_margin
PrefixCount.transportQeq1Goal_of_margin
PrefixCount.admissiblePartsCountBranchGoal_of_margin
PrefixCount.signedVal_ge_neg_two
PrefixCount.SignedMarginMatrix.sigma_sum_eq_zero
PrefixCount.MarginPlan.sigma_sum_eq
PrefixCount.MarginPlan.sigma_sum_eq_zero_of_zero_sum
PrefixCount.SignedMarginMatrix.eps_ge_neg_two
PrefixCount.Qge2PlanBounds
PrefixCount.Qge2PlanBounds.step_nonneg
PrefixCount.MarginTransportQge2PlanGoal
PrefixCount.marginTransportQge2Goal_of_plan
PrefixCount.MarginPlanQge2Goal
PrefixCount.SignedMarginMatrixForQge2PlanGoal
PrefixCount.marginTransportQge2PlanGoal_of_plan_and_matrix
PrefixCount.StepNonnegCompatibility
PrefixCount.StepNonnegCompatibility.step_nonneg
PrefixCount.MarginTransportQeq1CompatibleGoal
PrefixCount.marginTransportQeq1Goal_of_compatible
PrefixCount.PMOneBase
PrefixCount.PMOneBase.PlusOneMatching
PrefixCount.MatchedPMOneMatrix
PrefixCount.MarginTransportQeq1MatchedPMOneGoal
PrefixCount.marginTransportQeq1CompatibleGoal_of_matchedPMOne
PrefixCount.PMOneBase.PlusFamily
PrefixCount.PMOneBase.PlusFamily.toBase
PrefixCount.PMOneBase.PlusFamily.toMatching
PrefixCount.MarginTransportQeq1PlusFamilyGoal
PrefixCount.marginTransportQeq1MatchedPMOneGoal_of_plusFamily
oddCoreHighModulusPrefixCountGoal_of_margins_and_geometry
oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1Margin_and_geometry
oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1Compat_and_geometry
oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1MatchedPMOne_and_geometry
oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1PlusFamily_and_geometry
oddCoreHighModulusPrefixCountGoal_of_qge2PlanParts_qeq1PlusFamily_and_geometry
odd_modulus_tori_all_dimensions_of_margins_geometry_and_small_packet_lift
odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1Margin_geometry_and_small_packet_lift
odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1Compat_geometry_and_small_packet_lift
odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1MatchedPMOne_geometry_and_small_packet_lift
odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1PlusFamily_geometry_and_small_packet_lift
odd_modulus_tori_all_dimensions_of_qge2PlanParts_qeq1PlusFamily_geometry_and_small_packet_lift
oddCoreHighModulusPrefixCountGoal_of_prefixCount
```

The count-branch algebra is being split into quotient/remainder branch
arithmetic, signed transportation, dense matrix admissibility, layer-count
realization, and the geometric root-flat/Hamilton lift.  The layer-count
realization part is now Lean-closed by Hall's theorem and induction on the
regularity degree.  Therefore the high-modulus public goal can now be closed
from two ingredients:

```text
signed transport construction for q >= 2 and q = 1
+ geometric prefix-count Hamilton criterion
```

The transport construction is now also exposed through a margin-facing
interface:

```text
row margin plan
+ signed correction matrix
+ per-cell nonnegativity
```

For the `q >= 2` transport branch, per-cell nonnegativity is now factored out:
if the margin plan guarantees `2 <= q - tau i` in every row, then every signed
entry in `{ -2, -1, 1, 2 }` is automatically allowed.

For the `q = 1` branch, per-cell nonnegativity is factored through
`StepNonnegCompatibility`: rows with `q - tau = 0` must have nonnegative
entries, rows with `q - tau = 1` must avoid `-2`, and rows with
`q - tau >= 2` are automatic from the signed-value lower bound.

The q=1 branch is now further reducible to a matched `±1` matrix certificate:
start from a `±1` matrix with column sums `-1`, choose one explicit `+1` in
each column, and upgrade those entries to `+2` to obtain zero signed column
sums.

The matched `±1` matrix is in turn reducible to plus sets of size `(d-1)/2` in
each numeric column, with an explicit injective mate inside each plus set.

### B. Small-Modulus Hall-Slack Packet-Lift Theorem

Lean-facing goal, with packet predicates abbreviated in ASCII:

```lean
def RoundComposite.Concrete.OddCoreSmallModulusSlackPacketLiftGoal : Prop :=
  forall {d m b : Nat},
    Odd d -> 11 <= d ->
    Odd m -> 3 <= m -> m < d ->
    StandardCayleySolved b m ->
    (packets : List (List Nat)) ->
    packets.length = b ->
    (packets.map List.length).sum = d ->
    PacketSums packets m ->
    PacketUnits packets m ->
    d - b > b ->
    m ^ b > m * d * (d - b) ->
    StandardCayleySolved d m
```

This one theorem should supply both:

- `d = 11`, `m < 11`, by taking `b = 5`;
- all odd `d >= 13`, `m < d`, by taking the closed seed-semigroup base `b`
  and the closed packet/Hall-slack witness.

Status: public interface and arithmetic adapters closed; construction theorem
still open.

## Already Closed

- D2 seed.
- D3 seed.
- D5 odd seed.
- D7 odd seed.
- D9 from `D3 * D3`.
- All-dimensional wrapper from odd core.
- Seed-semigroup base availability for odd `d >= 13`.
- Packet decomposition from `2*b < d <= 3*b`.
- Positive unit packet construction for odd `m`.
- Hall-slack arithmetic witness for the general small branch.
- D11-specific `b = 5` Hall-slack arithmetic adapter.
- Prefix-count foundational algebra and transport interfaces.
- High-branch Lean adapter from admissible prefix-count parts and geometric
  criterion to `OddCoreHighModulusPrefixCountGoal`.
- High-branch Lean adapter from `TransportQge2Goal`, `TransportQeq1Goal`, and
  the geometric criterion to `OddCoreHighModulusPrefixCountGoal`.
- Top-level conditional dispatcher from those transport/geometry inputs plus
  the small-modulus Hall-slack packet lift to the all-dimensional theorem.
- Margin-facing transport interfaces and adapters from margin plans plus signed
  correction matrices to the two transport goals.
- Top-level conditional dispatcher from margin-facing transport inputs,
  geometry, and small packet lift to the all-dimensional theorem.
- Q>=2 plan-bounds adapter reducing q>=2 transport nonnegativity to the row
  condition `2 <= q - tau i`.
- Q=1 compatibility adapter reducing q=1 transport nonnegativity to row-local
  restrictions on where negative entries can appear.
- Q=1 matched `±1` adapter reducing q=1 signed corrections to an explicit
  columnwise upgrade certificate.
- Q=1 plus-set-family adapter reducing q=1 base columns to cardinality
  `(d-1)/2` plus sets.
- Signed-margin total-sum invariants: every signed correction matrix forces
  `sum sigma = 0`, and a margin plan has `sum sigma = m - sum zero`.
- Matrix-layer realization for balanced dense count matrices, including the
  zero case, Hall extraction of a positive permutation, one-layer peeling, and
  induction on the row/column degree.

## Non-Goals For This Stage

- Do not prove the final theorem by importing the `d < 29` finite boundary
  table.
- Do not make Route E or even-modulus D5/D7 work part of this goal.
- Do not reopen D7 as a construction target; use the current D7 odd theorem as
  a seed.
- Do not formalize the boundary witness table before the two public branch
  theorems above are fixed.

## Revised Goal In One Sentence

Prove all `d >= 2`, odd `m >= 3` by reducing even dimensions through the
D2/product wrapper, proving the odd core from the seeds `D3,D5,D7`, and closing
the two remaining uniform branches: high-modulus prefix counts and
small-modulus Hall-slack packet lifting.
