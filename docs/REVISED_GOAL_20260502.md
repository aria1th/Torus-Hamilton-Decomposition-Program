# Revised Goal

Date: 2026-05-02.

This note records the revised research goal after absorbing:

- `A5_exceptional_phase_splice_bundle_v0_4.zip`;
- `d5_even_routeE_branch_extraction_v0_7.zip`.

It is a planning target, not a completion claim.

## Regression Targets

Keep the already closed endpoints as regression targets:

- D7 odd torus/Cayley endpoint;
- D5 even Route-E endpoint interfaces, including the closed `m = 4` branch;
- D7 even behind the separate `RootFlatSchedule` interface.

The shared Lean infrastructure is treated as closed endpoint plumbing:

- composite/product infrastructure;
- root-flat lift;
- local additive bridge;
- skew-product monodromy;
- rank-cycle and Cayley/Torus wrappers.

New mathematical propositions should plug into these interfaces rather than
redesigning the endpoint layer.

## Program 1: D7 Odd `A7 ~= A5 x A3`

The D7 odd goal is a structural explanation of the existing D7 endpoint by the
additive `4+2` bridge.

### Target A1: Good-Class A5 Base

Use the `23/32` branch for odd `m` with `m % 5 != 2`.

Required deliverables:

- prove Q-hitting for the `23/32` section return;
- prove the Q-first-return formulas in Lean;
- prove the length-sum identity;
- package the relevant small odd moduli.

The quotient arithmetic is already closed in Lean: `phi_h` is a single cycle
iff `h % 5 != 3`, equivalently `m % 5 != 2`.

### Target A2: Exceptional A5 Base

For the exceptional class

```text
m = 10*t + 7,
```

use the five-lane phase-splice system from the exceptional bundle.

Required deliverables:

- formalize the five unequal lanes;
- formalize the `00` correction-block phase table;
- find a correction word or row-family insertion schedule;
- prove that the reduced five-lane map is one cycle;
- lift the splice proof back to Q-hitting, length-sum/excursion coverage, and
  the `m^4` base rank-step.

### Target A3: A5 Assembly

Combine the good and exceptional base branches into the concrete Target-A
package required by the `4+2` bridge.

Required deliverables:

- seven all-zero-set base rows;
- column exact-cover proof;
- folded A5 base return rank step into `ZMod (m^4)`.

### Target B'

After the row schedule is fixed, prove a compatible A3 fiber theorem.

Required deliverables:

- a zero-set-only or congruence-family `K_m(Z)`;
- triangular A3 round-return equation;
- scalar unit/carry theorem;
- fiber rank-step into `ZMod (m^2)`;
- lowering through the existing `4+2` bridge to D7 torus/Cayley.

## Program 2: D5 Even Route-E Branch Menu

Keep:

- the finite `m = 4` Route-E branch closed;
- the `Theta` small-seam certificate as the all-large endpoint;
- the existing D5 Hamilton/Torus/Cayley lowering infrastructure.

Replace:

- do not pursue one global count/drift formula as the main target;
- do not treat the origin-excursion affine chart as the top-level target.

New target:

- extract a finite residue-branch menu covering all even `m >= 6`;
- use B20, `m == 20 mod 24`, as the first symbolic branch;
- for each branch prove:
  - count formula;
  - `Theta` first-return equation;
  - no-earlier-return/minimality;
  - seam rank or single-cycle proof;
  - return-time sum `m^4`.

For B20 specifically:

```text
m = 24*q + 20,
h = m/2,
r = (h-1)/3,
nu = (r,0,0,h+r,r).
```

The expected seam map is:

```text
1 <= a <= h-2:      V(a) = a + h + 1 mod m
h-1 <= a <= m-1:    V(a) = a + h + 2 mod m
```

The missing theorem is the symbolic port-time/first-return proof plus
`sum tau = m^4`.

## Program 3: D7 Even

D7 even remains separate.

Required deliverables:

- keep the `RootFlatSchedule` certificate route isolated;
- do not reuse the D7 odd `4+2` bridge as an even proof;
- supply a D7-even-specific root-flat schedule family in a future bundle.
