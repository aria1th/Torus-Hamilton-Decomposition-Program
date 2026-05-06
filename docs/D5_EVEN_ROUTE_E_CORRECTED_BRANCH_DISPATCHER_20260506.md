# D5 Even Route E Corrected Branch Dispatcher

Date: 2026-05-06.

This note records the corrected proof target after the sign audit of the
adjacent-switch Route-E ansatz.

## Corrected Verdict

The following restricted branch is removed:

```text
cyclic bulk + RF2-preserving adjacent-rank Kempe repairs only.
```

It cannot prove even-modulus `D_5`.  The viable even branch is instead:

```text
full layered parity-changing one-layer coloring
+ nested first-return/splice certificate.
```

Here "one-layer coloring" means a proper edge-coloring of the root-flat layer
graph satisfying both outgoing and incoming Latin conditions.  It is not just a
pointwise stop transposition rule.

## One-Layer RF2 Condition

In `D_5`, write the root-flat prefix space as

```text
Q4 = (Z/mZ)^4
```

with stop vectors

```text
p0 = (0,0,0,0)
p1 = (1,0,0,0)
p2 = (1,1,0,0)
p3 = (1,1,1,0)
p4 = (1,1,1,1).
```

For a fixed layer, let

```text
c(z,r) = kappa    iff    color kappa uses stop r at root point z.
```

RF1 is:

```text
r |-> c(z,r) is a permutation of {0,1,2,3,4} for every z.
```

RF2 is equivalently:

```text
r |-> c(y + p_r, r) is a permutation of {0,1,2,3,4} for every y.
```

Thus each valid layer is a two-sided Latin object:

```text
outgoing Latin at tails + incoming Latin at heads.
```

This is the local condition any full layered branch must verify.

## Layer Sign Identity

For one layer define

```text
Lambda_t = product_kappa sign(P_{t,kappa}),
```

where `P_{t,kappa}` is the color-`kappa` root-flat layer map.  Let

```text
alpha_z : r |-> c(z,r)
beta_y  : r |-> c(y + p_r, r)
T_r(z)  = z - p_r.
```

Then:

```text
Lambda_t
 = (product_r sign(T_r))
   (product_z sign(alpha_z))
   (product_y sign(beta_y)).
```

This follows by comparing the permutation of the layer edge set in
tail-rank coordinates with the same edge set in tail-color/head-color
coordinates.

For even `m`, every prefix translation `T_r` has sign `+1` on `Q4`: nonzero
translations are products of `m^3` many `m`-cycles, and `m^3` is even.
Therefore layer parity is entirely controlled by the outgoing/incoming local
Latin signs.

## Global Sign Requirement

For even `m`, `|Q4| = m^4` is even.  If RF3 holds, every color return map is a
single `m^4`-cycle and hence has sign `-1`.  With five colors:

```text
product_kappa sign(R_kappa) = (-1)^5 = -1.
```

Since

```text
R_kappa = P_{m-1,kappa} ... P_{0,kappa},
```

any even `D_5` certificate must satisfy:

```text
product_t Lambda_t = -1.
```

Equivalently, an odd number of layers must carry negative layer parity.

## Adjacent-Kempe Branch Removal

An RF2-preserving adjacent `r/(r+1)` switch from cyclic bulk must be supported
on a set `A` satisfying

```text
A = A + e_{r+1}.
```

So the support is a union of full cycles in the affected coordinate direction.
Such a switch changes the two swapped color maps by the same sign factor, hence
does not change `Lambda_t`.  Cyclic bulk has `Lambda_t = +1`, and stacking only
these switches leaves every layer with `Lambda_t = +1`, contradicting the
global sign requirement.

Thus the old adjacent-switch-only branch is not a proof branch.  Adjacent words
remain useful only as local `S_5` descriptions of a defect layer.

## Remaining Even Branches

The corrected finite dispatcher is:

```text
Branch O:
  m odd.  Use the existing odd-modulus branch/input.

Branch E0:
  m = 2.  Use a full layered boundary certificate.
  Stationary seam certificates are excluded by sign/square obstructions.

Branch E-gen:
  m even and m >= M.  Use a full layered parity-changing one-layer coloring
  template.  The template must verify RF1, RF2, product_t Lambda_t = -1, and
  the four-level nested first-return/splice certificate for RF3.

Branch X:
  cyclic bulk + RF2-preserving adjacent-rank switches only.
  Removed by the sign obstruction.
```

## Finite Template Reduction

If a full layered template is described by finitely many affine seam predicates,
endpoint exceptions, and quasi-affine splice block boundaries, then verification
reduces to finitely many branches:

```text
small m < M,
and generic residue classes m mod L.
```

The reason is finite: RF1/RF2 depend on finitely many local predicate patterns;
seam overlaps and inverse detection reduce to finitely many linear congruence
systems; Smith normal form makes their solvability depend on fixed gcd/residue
data; and splice boundary order types are quasi-affine in `m`.  On each residue
branch, the return-time sums become polynomial or quasi-polynomial identities.

The next extraction target from SAT/finite witnesses is therefore not an
adjacent-switch slab list.  It is a parity-changing layer type list, its layer
parity table, the generic residue modulus `L`, and the RF3 splice tables.
