# D5 Even Route E Full-Layered Certificate Target

Date: 2026-05-06.

This note records the current proof target after the stationary/full-layered
SAT split.

## Key Observation

Two small-model facts should be kept separate:

```text
stationary seam SAT at m=2: UNSAT
full layered root-flat SAT at m=2: SAT
```

The first fact does not refute `D_5(2)`, nor does the second prove the generic
Route-E branch.  Together they say that the stationary seam normal form is the
wrong proof class.  Route E must be a full layered root-flat certificate.

## Stationary Square Obstruction

Let `m = 2`.  If a color uses the same root-flat layer map in both layers,

```text
P_{0,kappa} = P_{1,kappa} = P,
```

then its two-layer return is `R_kappa = P^2`.

No square of a permutation of a 16-point set can be a single 16-cycle.  On a
cycle of length `ell`, the square splits into `gcd(ell,2)` cycles.  A 16-cycle
squares to two 8-cycles, and no longer cycle can occur on a 16-point set.

Thus any proof class that forces `R_kappa` to be a layer-stationary square at
`m = 2` is structurally too small.

This is a warning, not the final theorem: the generic target may still start at
`m >= 4` or `m >= 6`.  The point is that layer-dependence is not cosmetic; it
is the mechanism that avoids even-modulus parity splitting.

## Full Layered Route-E Field

For `D_5(m)`, use prefix root-flat coordinates

```text
Q4 = (Z/mZ)^4
p0 = (0,0,0,0)
p1 = (1,0,0,0)
p2 = (1,1,0,0)
p3 = (1,1,1,0)
p4 = (1,1,1,1)
```

A full layered Route-E field is a function

```text
a_t(z,kappa) in {0,1,2,3,4}
t in Z/mZ, z in Q4, kappa in Z/5Z.
```

It defines layer maps

```text
P_{t,kappa}(z) = z - p_{a_t(z,kappa)}
```

and return maps

```text
R_kappa = P_{m-1,kappa} ... P_{0,kappa}.
```

The proof target is exactly:

```text
RF1: for every (t,z), kappa |-> a_t(z,kappa) is a permutation;
RF2: every P_{t,kappa} is a bijection of Q4;
RF3: every R_kappa is one m^4-cycle.
```

Once these hold, the existing root-flat certificate theorem gives a Hamilton
decomposition of `D_5(m)`.

## Nested First-Return Certificate

The preferred RF3 proof is not direct cycle enumeration.  It is the nested
first-return certificate:

```text
X0 = Q4
X1 = {u1 = 0}
X2 = {u1 = u2 = 0}
X3 = {u1 = u2 = u3 = 0}
X4 = {u1 = u2 = u3 = u4 = 0}.
```

The coordinates `u_i` may be adapted to the color and branch; they need not be
the raw prefix coordinates in the final symbolic proof.

At every level, prove:

```text
first-return map is a single cycle on the section;
sum of first-return times equals the ambient size.
```

Then the elementary first-return lemma lifts single-cycle-ness from `X4` back
to `X0`.

The diagnostic script currently uses the raw prefix flag and checks the exact
time sums:

```text
Q4 -> z1=0:                    m^4
z1=0 -> z1=z2=0:               m^3
z1=z2=0 -> z1=z2=z3=0:         m^2
z1=z2=z3=0 -> z1=z2=z3=z4=0:   m
```

## Finite-To-Symbolic Interface

SAT output should be used only to discover a finite symbolic template.  The
proof-facing template must contain:

1. affine or piecewise-affine seam families in `(t,z1,z2,z3,z4)`;
2. symbolic RF1 overlap checks;
3. explicit RF2 inverse formulas;
4. adapted clock coordinates for RF3;
5. finite block-splice permutations for every level and color;
6. polynomial return-time identities;
7. direct finite boundary certificates below the generic threshold.

If those are supplied, the full layered Route-E theorem is formal:

```text
full layered seam template
  + RF1/RF2 symbolic checks
  + nested single-cycle splice/time-sum certificates
  => D5 even Route E certificate
  => Hamilton decomposition of D5(m).
```

## Diagnostic Tool

Use

```bash
python3 scripts/analyze_d5_routeE_layer_dependence.py candidate.json
```

to check whether a JSON layer table is stationary or genuinely layer-dependent.
For the `m=2` SAT witness this should report non-stationary layer maps for the
successful full-layered certificate.  For any proposed stationary template, it
will show that each color return is just the repeated power of one layer map.

The script is a diagnostic only; passing it does not prove Route E.  Its role is
to prevent accidentally promoting a stationary seam artifact as a full layered
proof.

For local adjacent-switch extraction, use:

```bash
python3 scripts/analyze_d5_routeE_layer_switches.py candidate.json
```

This chooses each layer's modal local row as bulk and expresses every distinct
local row as a shortest word in adjacent stop-rank swaps.  On known
one-`Lambda_E` witnesses for `m >= 6`, it isolates exactly one defect layer
with 26 distinct rows.  On the `m=2` SAT witness, both layers are nonstationary
and locally more fragmented, reinforcing that `m=2` should be handled as a
boundary certificate unless a separate uniform formula is found.
