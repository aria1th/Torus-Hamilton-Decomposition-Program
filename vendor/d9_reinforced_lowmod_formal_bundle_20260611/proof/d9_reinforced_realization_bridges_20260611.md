# D9 reinforced realization bridges (2026-06-11)

This note records the semantic bridges added after the adversarial audit of the
D9 all-even certificate package.  The purpose is to make explicit which facts are
proved by the certificates and which facts are supplied by the uniform
realization lemmas.

## 1. Signed anchor-realization theorem

Let `D=9`.  Suppose a D9 anchor certificate supplies:

1. a terminal diagonal treeing;
2. simultaneous rooted coforest completions for every splice part;
3. for every pair part, a physical active edge whose descendant increment is
   `+1` or `-1` for both affected colors;
4. for every non-terminal triple part, two active edges for which the three
   affected-color increment vectors have pairwise determinant `±1`;
5. affine splice supports satisfying old-head transversality and support
   separation;
6. a terminal `A2` carrier separated from all splice traces;
7. an endpoint reserve in the complement of a protected neighborhood of the
   marked comparison cycle and of all existing splice traces;
8. the chain-field assembly data required by the next ordinary paired growth
   interface.

Then the certificate realizes `HED(9,m)` for every even modulus in the range in
which the placement and separation clauses are valid.

### Proof

The Latin row condition gives RF1.  Each localized exchange is supported on a
comparison-invariant support cylinder; hence the two-color or three-color local
switch lemma preserves layer bijectivity, giving RF2.  For a fixed color, the
rooted coforest completions give a laminar quotient flag.  The affine placement
ledger identifies the old heads on each support cylinder with the printed
quotient support line or plane.  Pair rows induce `j -> j ± 1` on the rank-one
quotient; since `±1` is a unit modulo every even `m`, these quotient splices are
cyclic.  Triple rows have primitive `A2` vectors, because every pair of active
vectors has determinant `±1`; after a unimodular change of active coordinates
they are the standard terminal `A2` splice packet.  The flag-splicing criterion
therefore makes the return cyclic on the final quotient.

Each final color forest is a one-isolate tree.  Adding the displayed closing
edge gives a spanning tree of the type-`A` root lattice, so the terminal closing
column is primitive.  The unit-carry lift converts the quotient cycle into one
root-flat return cycle.  The terminal `A2` carrier supplies the marked comparison
cycle, and the reserve verifier supplies the ordered endpoint reserve outside the
protected neighborhood and splice traces.  The chain-field table supplies the
label chart, row-indexed growth interface, midpoint translate rule, separated
terminal carrier, and fixed-old reserve form.  These are precisely the clauses of
`HED(9,m)`.

## 2. Terminal A2 semantic bridge

The terminal alignment is not merely a separated plane.  The reinforced verifier
checks that the terminal row is the shifted triple `(6,0,1)=(t,0,1)`, with
basis edges `(06,01)`, and that the terminal row vectors are exactly

```text
(-1,0), (1,1), (0,-1).
```

They sum to zero and have pairwise determinants `±1`.  The verifier also
recomputes the standard terminal word on sample even moduli and checks the
interlacing selector formula for `m >= 6`, and the small `m=4` selector using
terminal colors `(1,2)`.  The all-even cyclicity is the uniform terminal-A2
lemma; the script prevents transport or convention errors in the D9 data.

## 3. Protected-neighborhood convention

For the D9 anchor we use a conservative protected neighborhood: the entire
terminal carrier plane.  The marked comparison cycle produced by the terminal
`A2` block lies in that plane, and so do the terminal switch ribbons.  Thus it is
safe to require the endpoint reserve and all splice supports to be disjoint from
the whole terminal carrier plane.  The reinforced reserve verifier checks this
symbolically for `m > 9` through integer separating functionals and exhaustively
for `m = 4,6,8`.

## 4. Chain-field assembly

The D9 anchor is embedded into the next ordinary paired growth chart
`Z/11Z` with new labels `0` and `3`.  The chosen old-label embedding sends the
terminal carrier labels `{6,0,1}` to `{5,6,7}`, which are disjoint from the
ordinary paired growth window `{0,1,2,3,4,9,10}`.  The two ordinary row midpoint
collision sets are `{0,4}` and `{3,7}`.  The recorded phases have tested centers
`{5,6,7}` and `{9,10,0}`, respectively, and avoid those collision sets.
Therefore the corrected midpoint-collision paired-growth theorem can consume the
D9 output as an `HED(9,m)` input.
