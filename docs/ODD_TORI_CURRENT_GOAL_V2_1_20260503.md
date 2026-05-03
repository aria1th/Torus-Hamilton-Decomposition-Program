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
PrefixCount.MatrixAdmissible.toBalanced
PrefixCount.matrixLayerRealizationGoal_of_balanced
PrefixCount.MatrixLayerRealizationGoal
PrefixCount.layerRealization_of_matrixLayerRealizationGoal
PrefixCountLayerRealizationGoal
PrefixCountGeometricCriterionGoal
prefixCountLayerRealizationGoal_of_balancedMatrixLayerRealization
prefixCountLayerRealizationGoal_of_matrixLayerRealization
oddCoreHighModulusPrefixCountGoal_of_prefixCount
```

The count-branch algebra is being split into quotient/remainder branch
arithmetic, signed transportation, dense matrix admissibility, layer-count
realization, and the geometric root-flat/Hamilton lift.  Therefore the
high-modulus public goal can be closed from three ingredients:

```text
admissible parts construction
+ matrix layer decomposition for dense row/column count matrices
+ geometric prefix-count Hamilton criterion
```

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
- High-branch Lean adapter from admissible prefix-count parts, layer
  realization, and geometric criterion to `OddCoreHighModulusPrefixCountGoal`.
- Matrix-layer realization interface reducing layer realization to the
  permutation decomposition of dense admissible count matrices.
- Balanced-matrix split showing that the permutation-decomposition theorem only
  needs row/column regularity, not primitive prefix-count data.
- The zero-layer base case for balanced matrix layer realization.

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
