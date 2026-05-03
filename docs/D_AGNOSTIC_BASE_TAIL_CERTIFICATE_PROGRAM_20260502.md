# Dimension-Agnostic Base-Tail Certificate Program

Date: 2026-05-02.

Update 2026-05-03:

This is now a legacy finite-certificate/search design relative to
`docs/PREFIX_COUNT_ODD_TORI_OVERHAULED_V2_20260503.md`.  The v2 manuscript
uses a different base-tail proof architecture: a full-vertex skew product over
`X = (ZMod m)^(b+1)` plus active arcs carrying an extended prefix-count system,
with active Hall-slack realization.  The small-base-cycle plus tail-carry-unit
program below may still be useful for experiments and low-slack finite
certificates, but it is no longer the primary D11 proof route.

This note records the optimized finite certificate program suggested after the
D3 `A2` bridge rewrite and the D11 canonical schedule certificate.  The guiding
principle is:

```text
Do not check a huge cycle on (ZMod m)^(d-1).
Check a small base cycle and unit tail carries.
```

The purpose is twofold:

1. give a dimension-agnostic verifier design for future finite certificates;
2. audit whether D11 is already Lean-formalized in this repository.

## 1. Stop-Rank Coordinates

Let

```text
q = d - 1
Color = Direction = {0,...,q}
z = (z_0,...,z_{q-1}) in (ZMod m)^q
```

Use stop-rank `lambda in {0,...,q}` instead of choosing a direction directly.
The actual direction is

```text
dir(lambda) = q - lambda.
```

The prefix step for `lambda` is:

```text
z_j -> z_j - 1  iff  j < lambda.
```

Thus `lambda = 0` moves no prefix coordinate, while `lambda = r` moves exactly
`z_0,...,z_{r-1}`.

A schedule is a state-dependent permutation

```text
Lambda_t(z) : Color ~= {0,...,q}.
```

The Latin condition is then automatic: at every layer and state, colors receive
the stop ranks `0,...,q` exactly once.

## 2. Base-Tail Split

Choose a small base depth `b <= q`.  The recommended default is:

```text
b = 1                  if m >= d
b = ceil(log_m d)       if m < d
```

In practice, `b = 1,2,3` should usually be enough.  For the D11 leftover
moduli, the natural settings are:

```text
m = 5,7,9 : b = 2
m = 3     : b = 3
```

Let

```text
B = (ZMod m)^b.
```

For `ell = 0,...,b`, define

```text
v_ell = (1,...,1,0,...,0)
        with ell leading 1s.
```

The base projection identifies all `lambda >= b` as the same base move `v_b`.

## 3. Base Layer Certificate

For each layer `t` and base state `u in B`, choose the colors that receive the
early stop ranks:

```text
A_t(u, ell) in Color       for 0 <= ell < b.
```

For fixed `(t,u)`, the colors

```text
A_t(u,0),...,A_t(u,b-1)
```

must be distinct.  They receive `lambda = 0,...,b-1`; all remaining colors
receive a base-projected move `lambda >= b`.

For a fixed color `c`, define

```text
ell_c(t,u) =
  ell  if c = A_t(u,ell) for some ell < b
  b    otherwise.
```

Then the base layer map is

```text
P^(b)_{t,c}(u) = u - v_{ell_c(t,u)}.
```

## 4. BaseSimplex Condition

Instead of checking each `P^(b)_{t,c}` as a permutation by brute force, verify
the local simplex condition.

For every target `y in B`:

```text
{ A_t(y + v_ell, ell) : 0 <= ell < b }
  =
{ A_t(y + v_b, ell) : 0 <= ell < b }.
```

Both sides are unordered sets.

This is the local preimage uniqueness condition.  For each target `y` and
color `c`, among the possible preimage sources

```text
y + v_0, y + v_1, ..., y + v_b
```

exactly one source sends color `c` to `y`.

For `b = 2`, this becomes:

```text
v_0 = (0,0), v_1 = (1,0), v_2 = (1,1)

{ A_t((x,y),0), A_t((x+1,y),1) }
  =
{ A_t((x+1,y+1),0), A_t((x+1,y+1),1) }.
```

This is the diagonal-pair/simplex form that should make small-modulus layer
bank generation fast.

## 5. Base Return Condition

After choosing layers `A_0,...,A_{m-1}`, compute for each color:

```text
R^(b)_c = P^(b)_{m-1,c} o ... o P^(b)_{0,c}.
```

The base condition is:

```text
R^(b)_c is a single cycle on (ZMod m)^b
```

for every color `c`.

This is the only actual cycle enumeration in the verifier.  Its state count is
`m^b`, not `m^(d-1)`.

## 6. Tail Stop Certificate

For ranks

```text
r = b, b+1, ..., q-1
```

append one coordinate at a time.

Given a prefix state

```text
u = (z_0,...,z_{r-1}) in (ZMod m)^r,
```

let `S_r(t,u)` be the active colors that have not yet stopped at ranks
`0,...,r-1`.  Choose

```text
Stop_r(t,u) in S_r(t,u).
```

That color receives `lambda = r`, and the next active set is:

```text
S_{r+1}(t,u) = S_r(t,u) \ {Stop_r(t,u)}.
```

The last remaining color automatically receives `lambda = q`.  The Latin
condition is automatic by construction.

## 7. Tail Carry Units

Coordinate `z_r` decreases for color `c` exactly when `c` is still active after
rank `r`, i.e. when `c in S_{r+1}(t,u)`.

The total carry for color `c` at rank `r` is:

```text
C_{c,r}
  =
- sum_{t=0}^{m-1} sum_{u in (ZMod m)^r}
    1_{c in S_{r+1}(t,u)}
  mod m.
```

The required condition is:

```text
gcd(C_{c,r}, m) = 1.
```

Then the skew-cycle lemma upgrades

```text
R^(r)_c single cycle  ->  R^(r+1)_c single cycle.
```

Starting from the base cycle and applying this for `r=b,...,q-1` proves that
the full root-flat return is a single cycle on `(ZMod m)^q`.

## 8. Verifier Theorem

A raw certificate should be accepted when the deterministic verifier checks:

1. Base injectivity:

```text
A_t(u,0),...,A_t(u,b-1) are distinct.
```

2. Base layer bijectivity:

```text
BaseSimplex holds for every t,y.
```

3. Base return single cycles:

```text
R^(b)_c is a single cycle on (ZMod m)^b for every color c.
```

4. Tail carry units:

```text
gcd(C_{c,r}, m) = 1 for every c and r=b,...,q-1.
```

Conclusion:

```text
each color first-return map is a single cycle on (ZMod m)^q;
the original torus step moves the layer sum S by +1;
therefore the full color step is a single cycle of length m^d;
Latin gives the directed Hamilton decomposition.
```

## 9. Search Pipeline

The searcher can be heuristic; the verifier must be small and deterministic.

```text
solve(d,m):
  q := d - 1
  b := chooseBaseDepth(d,m)

  base_bank := generateBaseLayers(d,m,b)
  base_sequence := searchLengthMSequence(base_bank,d,m,b)
  tail_certificate := solveTailStops(base_sequence,d,m,b)

  return certificate(base_sequence, tail_certificate)
```

Verifier:

```text
verify(cert):
  check base injectivity
  check BaseSimplex
  compute base returns and check single cycles
  compute tail carries
  check each carry is a unit mod m
  reconstruct lambda schedule
  conclude Hamilton decomposition
```

## 10. Base Layer Generation

For `b = 1`, BaseSimplex forces the `lambda = 0` color to be base-state
independent.  This recovers the classical count-matrix branch and is natural
when `m >= d`.

For `b = 2`, BaseSimplex has the diagonal-pair form:

```text
{A_t((x,y),0), A_t((x+1,y),1)}
  =
{A_t((x+1,y+1),0), A_t((x+1,y+1),1)}.
```

This should be generated by diagonal pair/orientation data.

For general `b`, layer generation is an exact-cover problem:

```text
assign an ordered injective b-tuple to each u in (ZMod m)^b
subject to all simplex constraints.
```

This fits CP-SAT, exact cover, or Algorithm X.

## 11. Base Sequence Search

Each base layer `L` carries color permutations:

```text
perm[L][c] : Fin (m^b) -> Fin (m^b).
```

For a sequence `L_0,...,L_{m-1}`, compute:

```text
R^(b)_c = perm[L_{m-1}][c] o ... o perm[L_0][c].
```

Recommended score:

```text
sum_c (#cycles(R_c) - 1)
  + alpha * sum_c (m^b - largestCycle(R_c)).
```

Useful mutations:

```text
1. replace one layer
2. flip one simplex orientation inside a layer
3. apply a global color-relabel conjugation
```

Symmetry reductions:

```text
fix the first layer origin tuple
fix colors 0,...,b-1 at lambda 0,...,b-1
quotient cyclic shifts of the layer sequence
```

Layer sequence cyclic shifts preserve single-cycle status by conjugacy.

## 12. Tail Search as Modular Assignment

Tail ranks should not enumerate the whole prefix space when a small partition
suffices.  Each cell `E` stores:

```text
weight(E) = |E| mod m
active(E) = active color bitset
```

Choose a stop color:

```text
a_E in active(E).
```

For each color:

```text
C_{c,r} = B_c + sum_{E : a_E = c} weight(E),
```

where

```text
B_c = - sum_E weight(E) * 1_{c in active(E)}.
```

Thus each rank is a small modular assignment problem:

```text
choose a_E in active(E) so every C_{c,r} is a unit mod m.
```

For prime `m`, this means `C_{c,r} != 0`.  For composite `m`, use the unit
residue set, for example:

```text
m = 9  : {1,2,4,5,7,8}
m = 15 : {1,2,4,7,8,11,13,14}
```

## 13. Tail Partition DSL

Cells of size divisible by `m` contribute zero to carry modulo `m`, so they may
be aggressively merged.

A good compact DSL is a decision tree over predicates such as:

```text
z_i = t + a
z_i != t + a
z_i = z_j + a
active contains color c
```

with leaves returning a stop color from the active set.  The verifier compiles
the decision tree to a finite-domain BDD/MDD and computes each leaf cardinality
modulo `m`.

The canonical hit/no-hit split explains the older count formulas:

```text
z_r = t      has weight 1
z_r != t    has weight m - 1 == -1 mod m
```

## 14. Raw Certificate Format

Preferred raw format:

```text
Certificate(d,m):
  q = d - 1
  b = base depth

  Base:
    layers t = 0,...,m-1
    for each t:
      A_t : (ZMod m)^b -> InjectiveTuple(Color,b)

  Tail:
    for r = b,...,q-1:
      partition / decision tree description
      Stop_r : cell -> active color

  Witness:
    optional precomputed base return cycles
    optional carry residues C[c,r]
```

The verifier must recompute all witness data.  Witness fields are for debugging
and fast failure diagnosis only.

## 15. D11 Application

Legacy application from 2026-05-02.  The current v2 manuscript no longer uses
this finite-search route as the primary D11 small-case proof; it uses the
full-vertex base-tail Hall-slack theorem with base `b = 5`.

For D11:

```text
d = 11
q = 10
```

The external D11 canonical schedule certificate covers all odd `m >= 11` by a
`b = 1` count-matrix style construction.  It leaves

```text
m = 3,5,7,9
```

as finite small cases.  The base-tail program suggests:

```text
m = 5 : b = 2, base states = 25
m = 7 : b = 2, base states = 49
m = 9 : b = 2, base states = 81
m = 3 : b = 3, base states = 27
```

Recommended D11 small-case workflow:

```text
1. generate a b=2 diagonal/simplex base layer bank for m=5,7,9
2. search length-m base sequences
3. check base return single cycles
4. solve tail ranks r=b,...,9 as modular assignment
5. run the deterministic verifier
```

For `m = 3`, try `b = 2` only as a quick experiment; `b = 3` is the more
stable target because `3^2 < 11`.

## 16. D11 Lean Status Audit

Conclusion:

```text
D11 is not yet Lean-formalized as a theorem in this repository.
```

What exists:

- `D7Odd/Handoff/PrimeRoot.lean` defines a reusable
  `PrimeRoot.PrimeDimension` abstraction.
- `D7Odd/Handoff/PrimeCanonicalData.lean` defines dimension-parametric
  count-matrix and word-certificate structures.
- `D7Odd/Handoff/PrimeRootFlat.lean` defines dimension-parametric root-flat
  schedules and certificates.
- The D7 canonical theorem is closed and builds.

What is still D7-specific:

- `PrimeRoot.lean` defines `seven : PrimeDimension`; it does not define
  `eleven`.
- `CanonicalFamily.lean` is hard-coded to `Fin 7`, `Fin 6`, `RootState7`,
  `Vec7`, and D7 prefix coordinates.
- `CanonicalCountMatrices.lean`, `CanonicalSchedules.lean`, and
  `CanonicalWords.lean` are fixed to seven colors/symbols.
- Endpoint wrappers are named only for `D5` and `D7`, plus shared composite
  adapters.  There is no `D11Odd/` module and no theorem of type
  `Shared.CayleyHamiltonDecomposition 11 m`.

Verified during this audit:

```text
lake build D7Odd.Handoff.PrimeRoot
           D7Odd.Handoff.PrimeCanonicalData
           D7Odd.Handoff.PrimeRootFlat
           D7Odd.Handoff.CanonicalFamily
```

completed successfully.  This confirms the existing D7/generic infrastructure
is green, but it does not constitute a D11 proof.

## 17. D11 Formalization Work Remaining

To turn the external D11 certificate into Lean:

1. Add `PrimeDimension.eleven` and D11 simp/equivalence lemmas.
2. Add D11 count matrices and explicit base layer decompositions for odd
   `m >= 11`.
3. Prove the D11 `b=1` triangular return/carry theorem from the certificate.
4. Add finite/base-tail certificates for `m = 3,5,7,9`.
5. Add D11 root-flat, torus, and Cayley endpoint wrappers, or generalize the
   shared endpoint theorem enough to state `Shared.CayleyHamiltonDecomposition
   11 m` directly.

The fastest rigorous path is not to generalize all of `CanonicalFamily.lean`
at once.  First formalize D11 as its own instance using the new base-tail
certificate interface; generalize only the pieces that clearly pay for
themselves.
