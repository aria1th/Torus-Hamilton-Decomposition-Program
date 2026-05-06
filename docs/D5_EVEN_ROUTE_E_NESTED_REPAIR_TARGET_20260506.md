# D5 Even Route E Nested Repair Target

Date: 2026-05-06.

This note fixes the next Route-E target.  It is not a construction and not a
proof claim.  Its purpose is to prevent the D5 even search from chasing
one-dimensional seam hits that do not scale to the full four-dimensional root
flat.

## Objective

For `D_5(m)` the root flat has four prefix coordinates:

```text
Q4 = (Z/mZ)^4.
```

The even-modulus Route-E target should therefore be treated as a four-level
nested clock/lane repair problem, not as a direct copy of the D3 one-clock
splice.

It should also be treated as a full layered problem.  A stationary seam rule
that ignores the layer coordinate is too narrow: at `m=2`, stationarity would
force a two-layer return of the form `P^2`, and no square of a permutation of
the 16-point root flat can be one 16-cycle.  The full layered SAT witness at
`m=2` is therefore useful as a warning that layer-dependence is essential,
even if the final generic theorem starts only at `m >= 4` or `m >= 6`.

The desired final object is a layer direction field

```text
a_t(z,kappa) in {0,1,2,3,4}
t in Z/mZ, z in Q4, kappa in {0,1,2,3,4}
```

such that:

```text
RF1: for every (t,z), kappa |-> a_t(z,kappa) is Latin;
RF2: for every (t,kappa), z |-> z - p_{a_t(z,kappa)} is a bijection of Q4;
RF3: for every kappa, the m-layer return map on Q4 is one m^4-cycle.
```

Here

```text
p0 = (0,0,0,0)
p1 = (1,0,0,0)
p2 = (1,1,0,0)
p3 = (1,1,1,0)
p4 = (1,1,1,1).
```

## No-Go For Pure Prefix Counts

The odd prefix-count certificate cannot solve even `m`.

For `d=5`, the prefix-count primitive criterion would require every color row
to have `N_0` a unit modulo `m`.  If `m` is even, this means every `N_0` is
odd.  With five colors, the column sum of symbol `0` would then be odd, but
local Latin gives total symbol-`0` usage exactly `m`, which is even.

Thus the even branch must break count-only dependence.  It needs a genuinely
state-dependent finite repair.

## Adjacent-Rank Switches

The basic local trade is an adjacent stop-rank switch:

```text
r <-> r+1.
```

Because

```text
p_{r+1} - p_r = e_{r+1}
```

using one-indexed coordinates, this switch changes only coordinate
`z_{r+1}` in the affected colors.  Therefore the natural triangular repair
grammar is:

| switch | affected coordinate | allowed dependency in a triangular ansatz |
| --- | --- | --- |
| `0/1` | `z1` | `t,z2,z3,z4` |
| `1/2` | `z2` | `t,z3,z4` |
| `2/3` | `z3` | `t,z4` |
| `3/4` | `z4` | finite lane data |

The dependency column is a design constraint.  Later repairs should not destroy
the earlier clock structure.

## Nested First-Return Gates

For a fixed color, let `R` be the `m`-layer return map on `Q4`.

Define:

```text
Sigma1 = {z1 = 0}
Sigma2 = {z1 = z2 = 0}
Sigma3 = {z1 = z2 = z3 = 0}
Sigma4 = {z1 = z2 = z3 = z4 = 0}.
```

The Route-E normal form should prove RF3 by four applications of the finite
first-return lemma.  The checker-facing gates are:

| level | ambient | section | required time sum |
| --- | --- | --- | --- |
| 1 | `Q4` | `Sigma1` | `m^4` |
| 2 | `Sigma1` | `Sigma2` | `m^3` |
| 3 | `Sigma2` | `Sigma3` | `m^2` |
| 4 | `Sigma3` | `Sigma4` | `m` |

At each level the first-return map must be a permutation of the section.  At
the bottom, the induced map on the singleton `Sigma4` is trivially one cycle;
the time sums then lift one-cycle-ness back upward.

In practice the first-return maps should be described by interval/block
splices.  A candidate is not proof-facing until its block transition graph is
a single cycle at every relevant level.

## Even Sign Gate

For even `m`,

```text
|Q4| = m^4
```

is even, so a primitive return map on `Q4` has sign `-1`.  With five colors,
the product of return signs must also be `-1`.

Since

```text
R_kappa = P_{m-1,kappa} ... P_{0,kappa},
```

any full candidate must satisfy the early diagnostic:

```text
prod_{t,kappa} sign(P_{t,kappa}) = -1.
```

If this fails, the candidate cannot be a D5 even Route-E certificate, regardless
of promising count or small-seam behavior.

## Implementation Gate

The generic diagnostic script is:

```bash
python3 scripts/d5_routeE_nested_diagnostics.py candidate.json
```

The JSON format is:

```json
{
  "m": 6,
  "layers": [
    [[0,1,2,3,4]]
  ]
}
```

The displayed snippet shows the nesting only.  A real input must have exactly
`m` layers, each layer must have exactly `m^4` rows, and every row must have
five stop ranks.  More precisely, `layers[t][z][kappa]` is the stop rank
assigned at layer `t`, root-flat index `z`, and color `kappa`.  Root-flat
indices are lexicographic base-`m` encodings of `(z1,z2,z3,z4)`.

The script checks:

```text
RF1 local Latin
RF2 layer bijectivity
prod sign(P_t,kappa) versus the primitive sign target
full return cycles for each color
nested first-return time sums and section cycle decompositions
```

Smoke test on the constant bulk assignment
`layers[t][z] = [0,1,2,3,4]` at `m=2` reports:

```text
rf1_ok=True
rf2_ok=True
sign_ok=False
time_ok=False at every nested level
```

This is the expected early failure: the bulk Latin rule is bijective but not a
Route-E repair.

## Search Policy

A D5 even Route-E ansatz is worth promoting only if it passes the following
sequence.

1. **Local form:** built from adjacent-rank switches over a finite or modular
   low-layer repair window.
2. **RF1:** local Latin is automatic or mechanically checked.
3. **RF2:** every layer/color map has an explicit inverse or passes the finite
   bijection checker.
4. **Sign:** the even sign product matches `-1`.
5. **Nested return:** the four first-return levels have the required time sums.
6. **Splice stability:** each level has a finite block-transition description
   whose graph is one cycle.
7. **No fragmentation:** if a residue branch repeatedly splits into new
   exceptional subbranches, mark that ansatz false instead of continuing to
   chase it.

This policy is stricter than the current small-seam probes.  Small-seam hits
can suggest repair atoms, but they do not by themselves establish a
four-dimensional Route-E branch.

## Immediate Next Targets

1. Build candidate generators that emit the JSON layer table expected by
   `d5_routeE_nested_diagnostics.py` for small even `m`.
2. Start with triangular adjacent-switch windows:

   ```text
   0/1 switches depending on (t,z2,z3,z4)
   1/2 switches depending on (t,z3,z4)
   2/3 switches depending on (t,z4)
   3/4 switches depending on finite z4 lane points
   ```

3. Use sign and RF2 as cheap early rejection before running full nested return
   checks.
4. Preserve negative controls whenever a tempting simple law passes several
   samples and then fails.  These are useful for pruning the search grammar.
