# D11 Odd Working Certificate Note

Date: 2026-05-02.

Update 2026-05-03:

This note is superseded as a D11 status document by
`docs/PREFIX_COUNT_ODD_TORI_OVERHAULED_V2_20260503.md`.  The v2 manuscript
replaces the old D11-small-case finite-search gap with a base-tail Hall-slack
lift from the uniform D5 theorem: for `m < 11`, use `b = 5`, `T = 6`, and
`11 = 3 + 2 + 2 + 2 + 2`.  Thus the statements below about
`m = 3,5,7,9` being open raw-certificate tasks should now be read as legacy
planning, not as the current primary proof route.

This is the working version of the D11 status.  It separates the part that is
already a non-Lean proof certificate from the part that still needs finite
search certificates.

Source:

- `/data/angel/repos/etc/D11_odd_canonical_schedule_certificate.md`
- `docs/D_AGNOSTIC_BASE_TAIL_CERTIFICATE_PROGRAM_20260502.md`
- `docs/D11_LEAN_HELPER_LEMMA_REQUESTS_20260502.md`

## Status Summary

Legacy status from 2026-05-02.  Current v2 status: D11 is closed outside Lean
under the uniform D5 input; the small cases use the base-tail Hall-slack lift,
not raw finite-search certificates.

The D11 odd problem should be treated as:

```text
large branch m odd, m >= 11:
  mathematically closed outside Lean, pending Lean formalization

small cases m = 3,5,7,9:
  not covered by the canonical count method
  should be solved by the general base-tail search certificate program
```

So the current D11 theorem is not yet fully closed, but the remaining gap is
finite and programmatic.

## Large Branch: What Is Closed

For all odd `m >= 11`, the external certificate gives:

1. root-flat coordinates

```text
Sigma = {x in (ZMod m)^11 : sum_i x_i = 0}
Sigma ~= (ZMod m)^10
```

2. stop-rank coordinates

```text
lambda in {0,...,10}
dir(lambda) = 10 - lambda
z_j -> z_j - 1 iff j < lambda
```

3. canonical layer rule

```text
rho(t,z) = first rank 1..9 where z_{rho-1} = t,
           or 10 if no such rank exists
```

4. symbol permutation rule

```text
lambda_rho(0) = 0
lambda_rho(1) = rho
lambda_rho(s) = s      if s >= 2 and rho < s
lambda_rho(s) = s - 1  if s >= 2 and rho >= s
```

5. layer selectors

```text
delta_c(x) = dir(lambda_{rho(S,z)}(sigma_S(c)))
```

6. count-matrix branches covering all odd `m >= 11`

```text
m = 11 + 10h : B1  + h * Block10
m = 13 + 10h : B3  + h * Block10
m = 17 + 10h : B7  + h * Block10
m = 19 + 10h : B9  + h * Block10
m = 25 + 10h : B5  + h * Block10
m = 15       : B15
```

7. primitive row criterion

```text
gcd(N_0, m) = 1
gcd(N_k - N_1, m) = 1 for 2 <= k <= 10
```

8. triangular return theorem

```text
R^(1)(z_0) = z_0 + N_0
R^(r+1)(u,a) = (R^(r)(u), a + F_r(u))
sum_u F_r(u) = (-1)^r * (N_{r+1} - N_1)
```

9. skew-cycle induction

```text
primitive row criterion
  -> single cycle on (ZMod m)^10
  -> full color cycle of length m^11 on (ZMod m)^11
```

10. Latin edge partition

At each vertex, `c -> delta_c(x)` is a permutation of the eleven directions.
Thus the directed positive arcs are partitioned by the eleven colors.

## Large Branch Audit

An independent Python parse/check of the external markdown table confirmed:

```text
B1, B3, B7, B9, B5, B15:
  row sums match base length
  column sums match base length
  explicit layer lists are permutations
  explicit layer lists reproduce the matrices
  primitive row condition holds at the base length

Block10:
  row sums = column sums = 10

sample h = 0..59 for infinite branches:
  row sums and column sums match m
  primitive row condition holds
```

This audit checks the finite data in the document.  The symbolic part remains
the written triangular-return and skew-cycle proof, which is mathematically
standard and appears complete.

## Non-Lean Proof Status

For `m` odd and `m >= 11`, the D11 certificate should be considered
mathematically complete outside Lean, modulo ordinary write-up polishing.

Recommended polishing before publication or formalization:

1. State explicitly that each one-layer prefix map is bijective because
   `s -> lambda_rho(s)` is a permutation and each stop-rank step is invertible.
2. Split out the finite-map lemma:

```text
if f_m o ... o f_1 is bijective on a finite set,
then every f_i is bijective.
```

3. Clarify that the count-vector primitiveity proof is independent of the
   particular decomposition of the count matrix into layer permutations.
4. Choose one primary route for schedule existence:

```text
either Hall/perfect-matching decomposition,
or the explicit base layer lists plus Block10.
```

For Lean, the explicit layer lists are easier than formalizing Hall matching.

## What Is Not Closed

The document explicitly does not cover:

```text
m = 3,5,7,9
Lean formalization
```

Therefore the full D11 odd theorem

```text
for all odd m >= 3
```

is not closed yet.

## Small Cases: General Search Route

The small cases should not be handled by trying to extend the `b = 1`
canonical count method.  They are exactly where the general base-tail finite
certificate program is useful.

Use the dimension-agnostic certificate:

```text
small base cycle + tail carry units
```

instead of checking all of `(ZMod m)^10`.

For D11:

```text
d = 11
q = d - 1 = 10
```

Recommended base depths:

```text
m = 5 : b = 2, base states = 25
m = 7 : b = 2, base states = 49
m = 9 : b = 2, base states = 81
m = 3 : b = 3, base states = 27
```

The search output should be a raw certificate:

```text
Certificate(d=11,m):
  q = 10
  b = 2 or 3

  Base:
    layers t = 0,...,m-1
    A_t : (ZMod m)^b -> InjectiveTuple(Color,b)

  Tail:
    for r = b,...,9:
      small partition / decision tree
      Stop_r : cell -> active color

  Witness:
    optional base return cycles
    optional carry residues C[c,r]
```

The verifier must recompute everything and trust no witness field.

## Small Case Verifier Checks

For each `m = 3,5,7,9`, the deterministic verifier should check:

1. base injectivity

```text
A_t(u,0),...,A_t(u,b-1) are distinct
```

2. local BaseSimplex

```text
{A_t(y + v_ell, ell) : 0 <= ell < b}
  =
{A_t(y + v_b, ell) : 0 <= ell < b}
```

3. base return cycles

```text
R_c^(b) is a single cycle on (ZMod m)^b for every color c
```

4. tail carry units

```text
gcd(C_{c,r}, m) = 1
for every color c and rank r = b,...,9
```

Then the verifier concludes the full root-flat return is a single cycle on
`(ZMod m)^10`, and the full color step is a cycle of length `m^11`.

## Small Case Search Plan

For `m = 5,7,9`:

1. Generate the `b = 2` diagonal/simplex base layer bank.
2. Search length-`m` base sequences.
3. Score by the base return cycle profile:

```text
sum_c (#cycles(R_c) - 1)
  + alpha * sum_c (m^b - largestCycle(R_c))
```

4. Once base cycles close, solve tail ranks `r = 2,...,9` as modular
   assignment problems.
5. Emit raw certificates and run the deterministic verifier.

For `m = 3`:

1. Try `b = 2` only as a cheap experiment.
2. Expect `b = 3` to be the stable route.
3. Use the same pipeline, with base state count `27`.

## Tail Assignment Reminder

At rank `r`, compress the prefix space into cells `E` with:

```text
weight(E) = |E| mod m
active(E) = active color bitset
```

Choose one stop color:

```text
a_E in active(E)
```

Then

```text
C_{c,r} = B_c + sum_{E : a_E = c} weight(E)
```

and require `C_{c,r}` to be a unit modulo `m`.

For the small D11 moduli:

```text
m = 3 : units {1,2}
m = 5 : units {1,2,3,4}
m = 7 : units {1,2,3,4,5,6}
m = 9 : units {1,2,4,5,7,8}
```

## Lean Plan

Do not try to generalize all of the existing D7 `CanonicalFamily.lean` first.
It is heavily specialized to `Fin 7` and `Fin 6`.

Better order:

1. Implement a small external verifier/searcher for D11 small cases.
2. Store raw certificates for `m = 3,5,7,9`.
3. Add `PrimeDimension.eleven` and D11 endpoint wrappers.
4. Formalize the large-branch D11 count/carry theorem.
5. Add a Lean-facing certificate checker for the small raw certificates.

## Current Final Assessment

```text
D11 odd, m >= 11:
  closed outside Lean

D11 odd, m = 3,5,7,9:
  open finite certificate tasks
  search program is the intended solution

D11 Lean theorem:
  not yet formalized
```

This is now a well-scoped project: one formal large-branch translation plus
four finite search certificates.

## Lean Helper Lemma Requests

The requested Lean support lemmas are listed separately in
`docs/D11_LEAN_HELPER_LEMMA_REQUESTS_20260502.md`.  The list is organized as:

```text
generic finite dynamics
D11 coordinate lemmas
canonical layer rule
count matrix and branch arithmetic
triangular return lemmas
large-branch endpoint packaging
small-case base-tail certificate checker
```

The most important correction carried into that list is that the return map is
not claimed to be count-vector determined.  The theorem to formalize is that
the map is triangular and each total skew carry is count-vector determined.
