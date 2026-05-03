# Prefix-Count Odd Tori Overhauled v2 Absorption

Date: 2026-05-03.

Source bundle:

- `/data/angel/repos/etc/prefix_count_odd_tori_overhauled_v2_submission_bundle (1).zip`
- `prefix_count_odd_tori_overhauled_v2.tex`
- `prefix_count_odd_tori_overhauled_v2.pdf`
- `prefix_count_odd_tori_overhauled_v2_README.md`
- `prefix_count_odd_tori_overhauled_v2_checksums.txt`

This note records the structural changes from the v2 submission bundle.  It is
an absorption note, not a full proof audit.  Route E for D5 even is essentially
orthogonal to this bundle; the large changes are in the odd-torus prefix-count,
base-tail, D11, and eventual-dimension strategy.

## Executive Update

The proof program has shifted from D11-specific finite leftovers to two
dimension-generic mechanisms.

1. The prefix-count count branch proves directed Hamilton decompositions for
   every odd `d >= 5` and every odd `m >= d`.
2. The base-tail Hall-slack branch proves small-modulus cases from a solved
   lower base dimension `b`, using a full-vertex skew product and active
   prefix-count symbols.
3. D11 is no longer best treated as:

```text
m >= 11 closed, m = 3,5,7,9 open finite-search cases
```

Instead, the v2 manuscript treats D11 as closed outside Lean, conditional on
the known uniform D5 theorem:

```text
m >= 11: count branch
m = 3,5,7,9: base-tail Hall-slack lift from b = 5
```

The previous small-case raw certificate search remains useful as a sanity or
fallback path, but it is no longer the primary proof target for D11.

## Main Theorem Map

The manuscript organizes the proof around the following results.

Count branch:

```text
odd d >= 5, odd m >= d
--------------------------------
D_d(m) has a directed Hamilton decomposition
```

The finite arithmetic is no longer a D11-specific matrix table.  For
`m = (d-1)q + r`, the `q >= 2` range is handled by signed transportation with
entries in `{+/-1,+/-2}`; the `q = 1` range uses a restricted `{+/-1}` matrix
and a matching-based modification.

Base-tail Hall-slack branch:

```text
m < d odd
D_b(m) decomposable
d = k_1 + ... + k_b
each m is a sum of k_j positive units mod m
T = d - b, T > b, m^b > m d T
--------------------------------
D_d(m) decomposable
```

The introduction states the more readable condition `2 <= k_j <= m`, while
the final theorem uses the precise positive-unit decomposition condition.  In
the main corollaries only `k = 2` and `k = 3` are needed:

```text
2 = 1 + (m - 1)
3 = 1 + 1 + (m - 2)
```

for odd `m`.

D11 consequence:

```text
Assume D5(m) is decomposable for every odd m >= 3.
Then D11(m) is decomposable for every odd m >= 3.
```

For `m < 11`, use `b = 5`, `T = 6`, and

```text
11 = 3 + 2 + 2 + 2 + 2
3^5 = 243 > 3 * 11 * 6 = 198
```

so the Hall-slack inequality holds for `m = 3`, hence also for `m = 5,7,9`.

Eventual odd dimensions:

```text
Assume D3(m) is decomposable for every odd m >= 3.
Then every odd d >= 29 and every odd m >= 3 are solved.
```

The dimension choice uses a dyadic-triadic interval lemma: for every odd
`d >= 5`, there is `b in {2^a 3^e}` with `d/3 < b < d/2`.  With the composite
lift, this gives a solved base dimension `b`; for `d >= 29`, the inequality
`3^(d/3) > d^3` supplies the Hall slack.

## D2 Seed Audit

The dimension-two seed should not be left implicit.  It is the small solved
base that makes even composite base dimensions such as `6 = 2 * 3` and
`8 = 2^3` available.  Those even bases are exactly what remove apparent
low-modulus boundary cases such as `(d,m) = (13,3)`.

There is a direct uniform construction for `D_2(m)`.  For
`(x,y) in (ZMod m)^2`, set the phase

```text
s = x + y.
```

Use two factors.  In the first factor, take the horizontal edge when `s = 0`
and the vertical edge otherwise.  In the second factor, take the complementary
choice.  Every step increases `s` by `1`.  Over one phase lap:

```text
factor 0 uses the horizontal edge 1 time;
factor 1 uses the horizontal edge m - 1 times.
```

Both `1` and `m - 1` are units modulo `m`, so the phase return translates the
horizontal coordinate by a unit.  Hence both factors are Hamilton cycles, and
the two factors partition the two outgoing directions at every vertex.  This
works for every `m >= 2`, in particular for every odd `m >= 3`.

This is essentially the `k = 2` cylinder lemma in the smallest possible
dimension.  For the paper, it is better to state it explicitly as a seed lemma
instead of treating dimension `2` as folklore.

The finite boundary audit depends on whether this seed is included:

```text
seeds D3,D5 only:
  unresolved below d = 29 are (7,3), (7,5), (13,3), (17,3)

seeds D2,D3,D5:
  unresolved below d = 29 are (7,3), (7,5)

seeds D2,D3,D5,D7:
  no unresolved odd (d,m) with d < 29 and m < d
```

The earlier apparent `(13,3)` gap disappears by taking `b = 6 = 2 * 3`:

```text
d = 13, m = 3, T = 7
13 = 3 + 2 + 2 + 2 + 2 + 2
3^6 = 729 > 3 * 13 * 7 = 273
```

Thus `(13,3)` does not need its own finite certificate once `D2` and `D3` are
available and composite lift is allowed.

## Finite Determinacy Message

The most important conceptual value of the v2 manuscript is not just the
individual D11 consequence.  The stronger message is:

```text
Odd-dimensional directed torus Hamilton decompositions are reduced to
finite seed dimensions, finite low-modulus boundary checks, and the lifting
machinery of this paper.
```

With uniform seed decompositions in dimensions `2`, `3`, `5`, and `7`, the
current machinery proves every odd dimension `d >= 3` and every odd modulus
`m >= 3`:

```text
m >= d:
  prefix-count count branch

m < d, d >= 29:
  dyadic-triadic solved base + Hall-slack base-tail branch

m < d, d < 29:
  finite boundary audit using composite bases from D2,D3,D5,D7
```

If the paper wants to avoid taking uniform `D7` as an input theorem, then the
remaining finite boundary consists only of `D_7(3)` and `D_7(5)`.  Once those
two finite certificates are supplied, the same finite-determinacy conclusion
follows.  This is a stronger and cleaner headline than presenting D11 as the
main endpoint.

## Prefix-Count Core

The symbol set for dimension `d` is

```text
S_d = {0, Delta, 2, 3, ..., d-1}.
```

For a threshold-symbol word with counts

```text
N_0, N_Delta, N_2, ..., N_{d-1},
```

the primitiveity condition is:

```text
gcd(N_0, m) = 1
gcd(N_k - N_Delta, m) = 1 for 2 <= k <= d - 1
```

Then the prefix return map is a single cycle on the prefix space.

The v2 manuscript adds the extended theorem: the thresholds do not have to be
the canonical cyclic layer sequence.  Any finite threshold-symbol sequence of
length divisible by `m` works if the same count primitiveity conditions hold.
This is the key input for the active tail in the base-tail lift.

Lean relevance:

- the skew-cycle lemma should be generic;
- the prefix-count primitiveity theorem should be dimension-parametric if
  feasible;
- the extended theorem is now central, not optional.

## Base-Tail Architecture Changed

The older working design in
`docs/D_AGNOSTIC_BASE_TAIL_CERTIFICATE_PROGRAM_20260502.md` used:

```text
small base return + tail carry units
```

and was aimed at D11 small raw finite certificates.

The v2 manuscript uses a different proof architecture:

```text
base Hamilton decomposition on X = (ZMod m)^(b+1)
+ active arcs carrying a smaller prefix-count system
+ full-vertex skew-product lift
```

The base vertex set includes the layer coordinate and the first `b` prefix
coordinates.  It is not a root flat.  The remaining `T - 1`, with `T = d - b`,
coordinates form the active tail prefix space.

The base multigraph has:

```text
one copy of g_0, ..., g_{b-1}
T = d - b parallel active copies of g_b
```

A base-tail certificate consists of:

1. a decomposition of this base multigraph into `d` directed Hamilton cycles;
2. an active symbol assignment from `S_T = {0, Delta, 2, ..., T-1}`;
3. every base vertex sees each active symbol exactly once;
4. each base Hamilton cycle has active symbol counts satisfying the extended
   prefix-count unit conditions.

The lift is then a direct full-vertex skew product: one base lap returns to the
same base point and acts as a single cycle on the tail prefix space, so the
whole color map is a single cycle on the full vertex set.

## Active Hall-Slack Branch

The active symboling problem is formulated as a Hall-polytope realization.
For active incidence graph `Gamma`, active degree `T`, color active degrees
`A_c`, and active symbol count matrix `M`, the exact criterion is:

```text
row sums:    sum_sigma M[c,sigma] = A_c
column sums: sum_c M[c,sigma] = |X|
Hall cuts:   M(U,S) <= sum_x min(|A(x) cap U|, |S|)
```

The barycenter `B[c,sigma] = A_c / T` lies in the Hall polytope.  If `T > b`,
mixed-vertex slack is at least

```text
(m^b / T) * min(|S|, T - |S|)
```

on nontrivial cuts.

The universal residue table chooses units `u_c` with total zero:

```text
M[c,0]     ==  u_c mod m
M[c,Delta] == -u_c mod m
M[c,k]     ==  0   mod m for numeric k
```

For odd `d`, take one triple `1,1,-2` and fill the rest by pairs `1,-1`.
Controlled residue rounding keeps an integer matrix inside the Hall polytope
when `m^b > m d T`.

This branch is mathematically powerful but Lean-heavy: it imports finite
network-flow/Hoffman or equivalent Hall-realization reasoning plus a controlled
rounding theorem.

## What Is Superseded

The following earlier repository notes are now legacy relative to v2:

- `docs/D11_ODD_WORKING_CERTIFICATE_NOTE_20260502.md`
- `docs/D_AGNOSTIC_BASE_TAIL_CERTIFICATE_PROGRAM_20260502.md`
- `docs/D11_LEAN_HELPER_LEMMA_REQUESTS_20260502.md`
- the D11 part of `docs/D11_AND_A5_A7_LEAN_HANDOFF_PLAN_20260502.md`

They remain useful historical notes, but their D11 status should be read with
the v2 correction:

```text
old: D11 small cases m = 3,5,7,9 are open raw finite-search targets
new: D11 small cases are covered by base-tail Hall-slack from D5 input
```

The old dimension-agnostic finite verifier may still be useful for experimental
certificates in low-slack regimes, but it is not the manuscript v2 proof
architecture.

## Lean Formalization Backlog

The v2 Lean target is larger and more generic than the earlier D11-only plan.
The core requested Lean lemmas should be reorganized around these blocks.

Generic dynamics:

- `skew_cycle_of_total_carry_unit`;
- `full_layer_cycle_of_root_return`;
- permutation-form skew product over a one-cycle base and one-cycle return
  monodromy.

Root-flat and prefix coordinates:

- root-flat certificate theorem in dimension `d`;
- stop-rank/prefix coordinate step law;
- one-layer Latin factorization;
- one-layer prefix maps are bijections.

Prefix-count:

- prefix-count primitiveity theorem for cyclic layer words;
- extended prefix-count primitiveity theorem for arbitrary
  threshold-symbol sequences of length divisible by `m`;
- hit/no-hit counting modulo `m`, especially `(m-1)^r == (-1)^r`.

Count branch:

- prefix-admissible count matrix criterion;
- signed column capacity;
- signed transportation core for `q >= 2`;
- restricted `q = 1` construction;
- branch cover proving all odd `m >= d`.

Base-tail:

- base-tail full-vertex coordinate split
  `X x Q_(T-1) ~= (ZMod m)^d`;
- base-tail lift theorem;
- cylinder decomposition lemma;
- base cylinder expansion from `D_b(m)`.

Active Hall-slack:

- active Hall/Hoffman criterion or an equivalent finite assignment theorem;
- cylinder mixed-vertex slack;
- controlled residue rounding;
- universal residue table and unit-count conclusion;
- active Hall-slack realization theorem.

Consequences:

- composite lift;
- solved successor dimensions;
- D11 corollary from D5;
- dyadic-triadic interval-hitting lemma;
- eventual odd `d >= 29` corollary from D3.

For a pragmatic Lean order, first close the generic prefix-count path and the
D11 corollary using the already formalized D5 endpoint as an input theorem.
Then decide whether to formalize the Hall/Hoffman branch directly or encode a
more proof-assistant-friendly finite assignment certificate interface.

## Remaining Mathematical/Program Work

The manuscript itself lists three remaining directions.

1. Sharp active realization: replace the sufficient slack threshold
   `m^b > m d T` by the expected condition `A_c >= m`, probably via a
   residue-compatible exchange theorem inside the active Hall polytope.
2. Low-slack and low-dimensional boundary: use additional solved bases,
   optimized base-tail certificates, or direct finite constructions.
3. Formal verification: root-flat, prefix-count, signed transportation, and
   active Hall realization are finite/algebraic enough for Lean, but they are
   not yet formalized here.

## Current Strict Status

Outside Lean, under the manuscript's cited inputs:

```text
D5 uniform odd theorem -> D11 all odd m >= 3
D3 uniform odd theorem + composite lift -> all odd d >= 29, all odd m >= 3
count branch -> all odd d >= 5, odd m >= d
```

Inside this repository:

```text
D5 odd and D7 odd endpoints are formalized.
D11 is not yet a Lean theorem.
The v2 proof architecture has not been formalized.
The earlier D11 finite-search task should be treated as superseded, not false.
```
