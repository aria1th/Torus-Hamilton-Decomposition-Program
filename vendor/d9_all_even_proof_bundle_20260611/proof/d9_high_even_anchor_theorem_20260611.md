# D9 high-even anchor theorem (2026-06-11)

## Theorem
For every even modulus `m>9`, the verified D9 active anchor, its affine splice-placement ledger, and the terminal/reserve frame realize a high-even chain datum `HED(9,m)`.

## Inputs

1. `d9_active_anchor_candidate_v1.json`, verified by `verify_d9_active_anchor_candidate.py`.
   This supplies the D9 stage skeleton, one-isolate final forests, rooted coforest completions, signed pair-unit rows, primitive active A2 triple rows, and the terminal shifted triple `(6,0,1)`.
2. `d9_affine_splice_placement_ledger.json`, verified by `verify_d9_affine_splice_placement.py`.
   This supplies affine splice support cylinders, old-head transversality, active tail-head identities, and same-height separation for every splice support.
3. `d9_terminal_reserve_frame_candidate.json`, verified by `verify_d9_terminal_reserve_frame.py`.
   This supplies the terminal A2 carrier plane, terminal alignment, endpoint reserve plane, twelve reserve singleton sites, and projection separation from all splice traces.

## Proof

The active-anchor certificate gives the quotient coforest data.  For every color, the final graph is a one-isolate tree, and adjoining the displayed closing edge gives a spanning tree; the type-A tree incidence lemma therefore makes every closing column primitive.  Every pair row has descendant-coordinate increment `±1`, hence gives a cyclic rank-one splice over every even modulus.  Every non-terminal triple row has active vectors whose pairwise determinants are `±1`, hence is a primitive A2 splice after a unimodular active-coordinate change.  The final shifted triple is `(6,0,1)`, so the terminal carrier has the required `(t,0,1)` form with `t=6`.

The affine splice-placement ledger places each quotient support as an actual affine layer support cylinder.  For each affected color, contraction by the previously built forest sends the old-head image of the support cylinder to the printed support line or active support plane.  Inactive descendant coordinates and omitted exterior coordinates are constant, while active coordinates are exactly the signed pair-unit or primitive A2 coordinates from the active-anchor certificate.  The row-band functionals separate the four simultaneous splice parts at every used height; different heights are distinct for `m>9` because the shifts are `2,1,8,0,5,4,7`.

The terminal/reserve frame places the terminal A2 carrier on

`q_T + <06,01>`, with `q_T=(0,0,2,2,-4,0,0,0,0)`.

The chronological terminal triple is `(8,2,3)` at height `7`, so its shifted root vertices are `(6,0,1)`.  The terminal alignment rows are `(-1,0),(1,1),(0,-1)`, with permutation `(0,1,2)` and signs `(1,1,-1)`, matching the standard terminal A2 block.

The endpoint reserve is placed on

`q_R + <24,35>`, with `q_R=(3,4,3,5,-15,0,0,0,0)`.

The twelve reserve sites are the coefficient grid `{0,1,2,3} × {0,1,2}` on this plane.  They are pairwise distinct modulo every even `m>9` because all coefficient differences have entries of absolute value `<10` and the two reserve directions are independent.

For separation, the verifier supplies, for each pair of forbidden affine spaces, an integer functional `ell` that vanishes on both direction spans and has nonzero constant difference of absolute value at most `9`.  Hence the difference is nonzero modulo every `m>9`, so the spaces are disjoint.  This separates the terminal carrier from all splice supports, and separates the endpoint reserve plane from all splice supports and from the terminal carrier.

Thus all clauses of the anchor schedule realization criterion hold: Latin rows and RF2 layer bijectivity, old-head transversality, signed-unit tail-head successor identities, simultaneity and separation, primitive closing carries, terminal carrier, and endpoint reserve.  Therefore the schedule realizes a marked root-flat datum with endpoint reserve in dimension `9`.

The label chart is the cyclic chart `Z/9Z`.  The next ordinary paired growth interface uses the standard relabelling into `Z/11Z \ {0,3}`; the terminal carrier and endpoint reserve have been placed in fixed affine summands disjoint from splice traces, so the high-even chain fields are present.  Therefore the output is `HED(9,m)` for every even `m>9`.

## Remaining low-modulus gap
This theorem does not cover `m=4,6,8`.  The row-band and projection-separation proof uses nonzero integer differences of absolute value up to `9`, so it is uniform only for `m>9`.  The remaining unconditionality gap is therefore finite:

`HED(9,4)`, `HED(9,6)`, and `HED(9,8)`.
