# D5 Even Route E Adjacent-Kempe No-Go

Date: 2026-05-06.

This note isolates the negative result for a tempting but too narrow Route-E
ansatz.

## Verdict

The following restricted construction scheme cannot prove even-modulus `D_5`:

```text
cyclic bulk layer coloring
+ only RF2-preserving adjacent-rank Kempe repairs.
```

This does not prove that `D_5(m)` has no even-modulus Hamilton decomposition.
It also does not refute all full-layered Route-E fields.  It only rules out the
restricted idea that the even obstruction can be fixed by stacking local
RF2-preserving adjacent stop-rank switches on top of cyclic bulk.

The known one-`Lambda_E` witnesses avoid this no-go by using a globally
parity-changing defect layer.

## One-Layer RF2 Condition

Fix a layer and write the stop-to-color assignment as

```text
c(z,r) = kappa    iff    a(z,kappa) = r.
```

RF1 is the outgoing Latin condition:

```text
r |-> c(z,r) is a permutation for every z in Q4.
```

For RF2, fix an output `y`.  The possible incoming edges using stops
`r = 0,1,2,3,4` originate at

```text
y + p_r.
```

Thus each color must appear exactly once among those incoming stop choices:

```text
r |-> c(y + p_r, r) is a permutation for every y in Q4.
```

So a valid layer is a two-sided Latin object:

```text
outgoing Latin at z
+ incoming Latin at y.
```

This is why an arbitrary local adjacent swap preserves RF1 but need not
preserve RF2.

## Adjacent Switch Support Criterion

Start from a bulk layer where two colors use adjacent stops `r` and `r+1`.
Apply the `r <-> r+1` swap on a support set `A subset Q4`.

For one of the two colors, after factoring out the common translation, the
local map has the form

```text
F_A(z) = z - e_{r+1},  if z in A
       = z,            otherwise.
```

For an output `y`, the number of preimages is

```text
1_{y notin A} + 1_{y + e_{r+1} in A}.
```

Therefore `F_A` is bijective exactly when

```text
1_A(y) = 1_A(y + e_{r+1}) for every y,
```

or equivalently:

```text
A = A + e_{r+1}.
```

Thus an RF2-preserving adjacent `r/r+1` switch support must be a union of full
cycles in the affected coordinate direction:

```text
0/1 support independent of z1,
1/2 support independent of z2,
2/3 support independent of z3,
3/4 support independent of z4.
```

Point repairs and finite endpoint repairs in the affected coordinate are not
RF2-preserving by themselves.

## Sign Obstruction

For even `m`, each nonzero prefix translation on

```text
Q4 = (Z/mZ)^4
```

has sign `+1`: it is a product of `m^3` many `m`-cycles, and `m^3` is even.
The identity stop also has sign `+1`.  Hence a cyclic bulk layer has layer sign
product

```text
Lambda_t = product_kappa sign(P_{t,kappa}) = +1.
```

Now apply an RF2-preserving adjacent switch on `q` full affected-coordinate
cycles.  It changes each of the two swapped color maps by the same sign factor

```text
(-1)^{q*(m-1)}.
```

The product of the two color signs therefore changes by

```text
(-1)^{q*(m-1)} * (-1)^{q*(m-1)} = +1.
```

So RF2-preserving adjacent-rank switches cannot change the layer sign product.
Starting from cyclic bulk, every layer remains `Lambda_t = +1`.

## Conflict With RF3

If RF3 holds, each color return map is a single cycle on `Q4`.  For even `m`,

```text
|Q4| = m^4
```

is even, so each single `m^4`-cycle has sign `-1`.  There are five colors, so
the product of return signs must be

```text
(-1)^5 = -1.
```

But in the restricted adjacent-Kempe ansatz,

```text
product_kappa sign(R_kappa)
  = product_t product_kappa sign(P_{t,kappa})
  = product_t Lambda_t
  = +1.
```

This contradicts RF3.

## Consequence

The following proof strategy is false:

```text
cyclic bulk
+ RF2-preserving adjacent-rank repairs
+ nested first-return splice
=> D5 even Route E.
```

The viable target must include a parity-changing global layer coloring.  The
known one-`Lambda_E` witnesses have exactly this shape:

```text
constant bulk layers:      layer_sign = +1
one Lambda_E defect layer: layer_sign = -1
```

The adjacent-switch word analyzers are still useful, but only as local
`S_5` row descriptions of the Lambda_E layer.  They are not a construction by
RF2-preserving local Kempe repairs.

