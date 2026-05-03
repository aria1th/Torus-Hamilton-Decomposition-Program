# Odd-Modulus Tori Current Goal v2.2

Date: 2026-05-03.

This note is the current working goal after the `d < 29` boundary review, the
D2/product-wrapper review, and the latest prefix-count transport split.

## Final Target

Prove the all-dimensional odd-modulus theorem:

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Equivalently, every standard directed torus
`Cay((ZMod m)^d, {e_0, ..., e_{d-1}})` has a directed Hamilton decomposition
when `2 <= d`, `Odd m`, and `3 <= m`.

## Main Strategic Reset

The `d < 29` finite boundary table is not a theorem-level input in the current
proof spine.  It remains useful as audit/regression evidence, but the final
Lean theorem should not import it.

The revised proof spine is:

```text
D2 seed and product wrapper
+ odd-dimensional core seeds D3, D5, D7
+ D9 as D3 * D3
+ D11 by the same high/small branch split
+ high-modulus prefix-count theorem for odd d >= 5, m >= d
+ small-modulus Hall-slack packet lift for odd d >= 11, m < d
```

Thus `(d,m) = (13,3)` is not a distinguished leftover pair in the new spine.
It is covered by the uniform small-modulus packet-lift theorem once that
theorem is proved.  The same applies to the rest of the former `d < 29`
boundary list.

## Current Lean Endpoint

At the public level, the all-dimensional theorem is reduced to two theorem
families:

```lean
OddCoreHighModulusPrefixCountGoal
OddCoreSmallModulusSlackPacketLiftGoal
```

The current lowest-level endpoint is sharper.  It proves the final theorem
from the following five remaining blocks:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_qge2PlanParts_qeq1PlusFamily_geometry_and_small_packet_lift
    (hQge2Plan : PrefixCount.MarginPlanQge2Goal)
    (hQge2Matrix : PrefixCount.SignedMarginMatrixForQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

So the active Lean goal is to remove exactly these four assumptions.

## Remaining Blocks

1. `PrefixCount.MarginTransportQge2PlanGoal`

   Superseded at the lowest level by the next two goals, but retained as a
   useful bundled interface.

1a. `PrefixCount.MarginPlanQge2Goal`

   The row-margin part of the high-modulus quotient branch with `q >= 2`.
   It asks for `P : MarginPlan d m q r` satisfying `Qge2PlanBounds P`, namely
   `2 <= q - tau i` rowwise.

1b. `PrefixCount.SignedMarginMatrixForQge2PlanGoal`

   The signed-matrix realization part for q>=2 margin plans.  Once it supplies
   `SignedMarginMatrix d P.sigma`, `Qge2PlanBounds.step_nonneg` gives per-cell
   nonnegativity from the universal lower bound `eps >= -2`.

2. `PrefixCount.MarginTransportQeq1PlusFamilyGoal`

   The high-modulus boundary branch with `q = 1`.  This is now reduced to a
   plus-set certificate: construct row margins and, for each numeric column, a
   plus set of size `(d-1)/2` together with an explicit injective mate inside
   the plus set.  This gives a `±1` base matrix with column sums `-1`; upgrading
   each matched `+1` to `+2` gives the required signed correction matrix.  Rows
   with `q - tau = 0` must see only nonnegative base entries.

3. `PrefixCountGeometricCriterionGoal`

   The geometric prefix-count Hamilton criterion.  This should package the
   root-flat coordinates, the canonical layer rule, the Latin property, the
   triangular return/skew-cycle argument, the primitive row criterion, and the
   lift from first return cycles to Hamilton cycles on the full torus.

4. `OddCoreSmallModulusSlackPacketLiftGoal`

   The uniform base-tail theorem for `m < d`.  The required seed-semigroup base
   and Hall-slack arithmetic witnesses are already Lean-closed; the remaining
   work is the actual packet/base-tail lift construction.

## Closed Support

The following are already available as Lean-checked support for this goal:

- D2 seed and even-dimensional product wrapper.
- D3 seed, D5 seed, D7 seed, and D9 as `D3 * D3`.
- Seed-semigroup base availability for odd `d >= 13`.
- Unit packet construction and Hall-slack arithmetic witnesses.
- D11-specific `b = 5` Hall-slack arithmetic adapter.
- Prefix-count foundational algebra and quotient/remainder interfaces.
- Dense matrix layer realization, closed by Hall extraction and induction.
- Margin-facing transport adapters.
- Q>=2 nonnegativity adapter.
- Q=1 compatibility-to-nonnegativity adapter.
- Q=1 matched `±1` matrix adapter.
- Q=1 plus-set-family adapter, including nonemptiness of the plus-family
  certificate layer.

## Non-Goals

- Do not prove the final theorem by importing the `d < 29` finite boundary
  table.
- Do not treat `(13,3)` as a special certificate target unless the uniform
  small-modulus packet-lift theorem unexpectedly fails.
- Do not include Route E or even-modulus work in the active goal.
- Do not reopen D7 as a construction target; use the existing D7 odd endpoint
  as a seed.

## One-Sentence Goal

Close all odd `m >= 3` and all `d >= 2` by proving the two uniform branches
that remain after the D2/product wrapper and odd seed reductions: the
high-modulus prefix-count construction and the small-modulus Hall-slack
packet-lift construction, with the high branch currently split into q>=2
row margin plans, q>=2 signed matrix realization, q=1 plus-set margins, and
the geometric prefix-count criterion.
