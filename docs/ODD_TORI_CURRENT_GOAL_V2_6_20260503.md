# Odd-Modulus Tori Current Goal v2.6

Date: 2026-05-03.

This note records the current goal after the `d < 29` condition review.  It
supersedes `docs/ODD_TORI_CURRENT_GOAL_V2_5_20260503.md` as the concise active
goal reference.

The key reset is:

```text
The finite `d < 29` boundary table is not part of the proof spine.
```

It remains valuable as audit and regression evidence, but it should not be a
theorem-level input.  In particular, `(d, m) = (13, 3)` is no longer a special
terminal pair in the intended proof.  Once the uniform small-modulus
Hall-slack packet lift is proved, the former boundary pairs are absorbed by
the D2/D3 seed-semigroup base mechanism and the same lifting machinery used in
the general small branch.

## Final Target

Formalize the all-dimensional odd-modulus theorem:

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Equivalently, every standard directed Cayley torus
`Cay((ZMod m)^d, {e_0, ..., e_{d-1}})` has a directed Hamilton decomposition
for every `2 <= d`, odd `m`, and `3 <= m`.

The theorem is all-dimensional.  The hard constructive part is the
odd-dimensional core; even dimensions are handled by the D2 seed and the
product/composite wrapper.

## Current Proof Spine

The proof spine should be:

```text
D2 seed and product wrapper
+ odd seeds D3, D5, D7
+ D9 as D3 * D3
+ D11 from high-prefix-count for m >= 11 and D5-base slack lift for m < 11
+ high-modulus prefix-count theorem for odd d >= 5, m >= d
+ small-modulus Hall-slack packet lift for odd d >= 11, m < d
--------------------------------------------------------------------------
all d >= 2 and all odd m >= 3
```

For odd `d >= 13` and `m < d`, choose a solved seed-semigroup base `b`
generated from D2 and D3.  The arithmetic side is already Lean-closed:

```text
2*b < d <= 3*b
d - b > b
m^b > m*d*(d-b)
```

The remaining content is not a finite boundary table; it is the uniform
base-tail/Hall-slack lift theorem that consumes this solved base, unit-packet
data, and slack.

## Current Lean Endpoints

The manuscript-facing conditional endpoint is:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

The preferred lowest-level endpoint currently exposes four remaining
assumptions:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_qge2Compat_qeq1Compat_rootFlatCanonical_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1CompatibleGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Thus the active Lean goal is to remove exactly these four assumptions.

## Remaining Proof Blocks

1. `PrefixCount.MarginTransportQge2CompatibleGoal`

   Prove the q>=2 compatible signed transport construction.  The old global
   `Qge2PlanBounds` target is too strong; Lean records the obstruction at
   `q = 2, r = 1`.  The target should directly construct the margin plan,
   signed matrix, and compatibility proof together.

2. `PrefixCount.MarginTransportQeq1CompatibleGoal`

   Prove the q=1 compatible signed transport construction.  The pure
   plus-family target is not the final theorem family: Lean proves
   `PrefixCount.not_marginTransportQeq1PlusFamilyGoal` by the
   `d = m = 5, q = r = 1` instance.  The q=1 proof needs a richer compatible
   transport construction or a refined certificate interface.

3. `PrefixCountRootFlatCanonicalReturnGoal`

   Build the canonical root-flat prefix-count certificate: row Latin,
   layer bijectivity, single-cycle color returns, and equality with
   `prefixCountRootStep d m`.  The Cayley lift from such a canonical-step
   certificate is already Lean-closed.

4. `OddCoreSmallModulusSlackPacketLiftGoal`

   Prove the uniform small-modulus base-tail theorem from a solved base,
   unit-packet data, and Hall-slack inequalities.  The active Lean route goes
   through `RoundComposite/ActiveHall.lean`: feasible residue count matrices,
   Hall cuts, realization as symbolings, unit carry extraction, and then the
   base-tail Hamilton lift.

## What Is Already Closed

- D2 seed and the all-dimensional product wrapper.
- D3 seed, D5 seed, D7 seed, and D9 as `D3 * D3`.
- Seed-semigroup base availability for odd `d >= 13`.
- Unit-packet construction and Hall-slack arithmetic witnesses, including the
  D11 `b = 5` adapter.
- Dense matrix layer realization for balanced count matrices.
- Prefix-count quotient/remainder interfaces and margin-facing adapters.
- Q>=2 necessary bounds and the obstruction to the old global
  `Qge2PlanBounds` formulation.
- Q=1 range arithmetic, matched `+/-1` adapters, plus-family diagnostics, and
  the Lean proof that the pure plus-family global target is impossible.
- Root-flat equivalence and canonical-step Cayley lifts.
- Active-Hall foundations: cut cap/mass lemmas, nontrivial cut reduction,
  cut monotonicity, residue compatibility, ordinary Hall token matching,
  one-symbol quota token matching, and the converse from symbolings to feasible
  residue count matrices.

## Boundary Table Status

`docs/ODD_TORI_D_LT_29_BOUNDARY_WITNESSES_20260503.md` is an audit table, not
the main proof plan.  It should be used to check that the new uniform
small-modulus theorem covers the former finite boundary.  It should not be
imported into the final Lean theorem unless the uniform small branch fails and
the project intentionally falls back to explicit finite certificates.

Consequently:

- `(13, 3)` is not a distinguished open pair in the intended proof.
- There is no current plan to formalize all `169` former boundary pairs.
- The former boundary data remains useful for search, regression, and sanity
  checks.

## Immediate Working Goal

The next useful Lean work is:

```text
1. Continue reducing `OddCoreSmallModulusSlackPacketLiftGoal`
   through Active-Hall realization.
2. Keep the high branch focused on the compatible q>=2 and q=1 transport
   targets, not the obsolete plus-family or global-bound formulations.
3. Prove `PrefixCountRootFlatCanonicalReturnGoal` as the canonical geometric
   certificate endpoint.
```

## Success Criterion

The goal is complete only when the repository contains the non-conditional
Lean theorem

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

with no branch assumptions and no theorem-level dependency on the `d < 29`
finite boundary table.

## One-Sentence Goal

Prove all `d >= 2` and odd `m >= 3` by combining D2/product lifting, solved
odd seeds, the high-modulus prefix-count construction, and one uniform
small-modulus Hall-slack packet-lift theorem, with the former `d < 29`
boundary retained only as audit evidence.
