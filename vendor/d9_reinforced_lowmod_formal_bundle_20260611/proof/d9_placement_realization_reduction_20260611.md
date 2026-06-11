# D9 placement realization reduction (2026-06-11)

This note records the next rigorous reduction after the D9 active graph/coforest
anchor.  The active anchor supplies terminal treeing, simultaneous rooted
coforests, signed pair-unit rows, active A2 triple rows, and terminal form.  To
obtain a full HED(9,m) anchor, it remains to supply an affine placement
certificate.

## Signed anchor-schedule realization criterion

The original anchor-schedule realization definition used successor `+1`.  For
D9 the correct condition is successor by a unit.  In rank one, `+1` may be
replaced by `±1`; in rank two, the three triple increments may be any primitive
A2 triple, i.e. their pairwise determinants are `±1`.

### Lemma 1: signed rank-one placement

Let `H <= H + <a>` over `Z/mZ`, and suppose the old heads on a support line are
ordered by a descendant coordinate `lambda_a`.  If the localized row replaces
an old head by the head shifted by `epsilon a`, where `epsilon = ±1`, then the
splice on `(H+<a>)/H` is `j -> j + epsilon`, hence cyclic for every even `m`.

### Lemma 2: unimodular A2 placement

Let a triple row have active coordinate vectors `v0,v1,v2 in Z^2`.  If every
pair determinant is `±1`, then after a unimodular change of active coordinates
this is the standard A2 terminal/triple packet.  Consequently the two rank-one
splice steps are primitive over every `Z/mZ`.

## D9 affine placement certificate: required fields

For every stage `r`, row part `P`, and rank-one active substep `j`, a placement
certificate must provide:

1. an affine source cylinder/line `U_{r,P,j}` in the layer of height `s_r`;
2. its old-head image under the pre-row return for each affected color `c in P`;
3. the contracted quotient image of that old-head set;
4. the descendant-coordinate increment of the new head relative to the old head;
5. separation projections proving all splice traces, the terminal A2 carrier,
   and the endpoint reserve are disjoint except for prescribed simultaneous-row
   overlaps.

The active D9 verifier already proves the quotient increments in (4).  The
missing fields are the actual affine lift data (1)--(3) and the separation data
(5).

## Proposition: sufficiency of a D9 affine placement certificate

If the D9 active-anchor candidate v1 is supplemented by the affine placement
certificate above, then for every even `m >= 4` it realizes `HED(9,m)`.

Proof.  Latin/RF2 follows from the layer-comparison switch lemma on the listed
affine supports.  Old-head transversality and the signed successor identities
identify the return effect of each localized row with the signed rank-one or
unimodular A2 splice.  The rooted coforest completions give a laminar quotient
flag for each color, so the flag-splicing criterion makes the return cyclic on
final forest quotients.  Each final D9 forest is a one-isolate tree and its
closing edge is primitive; the unit-carry lift makes the full return a single
cycle.  The terminal row `(6,0,1)` supplies the terminal A2 marked selector, and
the separated reserve sites give the endpoint reserve.  The label chart,
row-indexed old spans, terminal carrier, and reserve form are exactly the high-even
chain fields, so the output is `HED(9,m)`.  □

## Status

This reduction is complete, but it is not itself the affine placement certificate.
The remaining proof object is now finite and explicit: a D9 placement ledger of
source lines/cylinders and separation projections.
